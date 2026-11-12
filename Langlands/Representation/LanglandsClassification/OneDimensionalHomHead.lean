import Langlands.Representation.Classification.ConstituentRelations
import Langlands.Representation.Category.Basic
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Strong irreducible heads from a one-dimensional Hom space

This is the algebraic kernel-uniqueness argument used in Renard VII.4.2 (i).
Existence of a quotient and embeddings into the comparison representation
remain explicit hypotheses.
-/

noncomputable section

namespace Langlands.Classification

universe uG uV uB uW₁ uW₂

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {B : Type uB} [AddCommGroup B] [Module ℂ B]
  {W₁ : Type uW₁} [AddCommGroup W₁] [Module ℂ W₁]
  {W₂ : Type uW₂} [AddCommGroup W₂] [Module ℂ W₂]
  {ρ : Representation ℂ G V} {β : Representation ℂ G B}
  {π₁ : Representation ℂ G W₁} {π₂ : Representation ℂ G W₂}

/-- Two nonzero maps which embed into a common comparison representation
have equal kernels when the comparison Hom space has dimension one.
All four carrier universes are independent. -/
theorem quotientKernels_eq_of_finrank_one
    (hdim : Module.finrank ℂ (ρ.IntertwiningMap β) = 1)
    (q₁ : ρ.IntertwiningMap π₁) (q₂ : ρ.IntertwiningMap π₂)
    (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0)
    (j₁ : π₁.IntertwiningMap β) (j₂ : π₂.IntertwiningMap β)
    (hj₁ : Function.Injective j₁) (hj₂ : Function.Injective j₂) :
    q₁.toLinearMap.ker = q₂.toLinearMap.ker := by
  have hcomp₁ : j₁.comp q₁ ≠ 0 := by
    intro h
    apply hq₁
    ext x
    change q₁ x = 0
    apply hj₁
    have hx := congrArg (fun f : ρ.IntertwiningMap β => f x) h
    change j₁ (q₁ x) = 0 at hx
    simpa only [map_zero] using hx
  have hcomp₂ : j₂.comp q₂ ≠ 0 := by
    intro h
    apply hq₂
    ext x
    change q₂ x = 0
    apply hj₂
    have hx := congrArg (fun f : ρ.IntertwiningMap β => f x) h
    change j₂ (q₂ x) = 0 at hx
    simpa only [map_zero] using hx
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdim hcomp₁ (j₂.comp q₂)
  have hc0 : c ≠ 0 := by
    intro h
    apply hcomp₂
    simpa only [h, zero_smul] using hc.symm
  ext x
  have hx := congrArg (fun f : ρ.IntertwiningMap β => f x) hc
  change c • j₁ (q₁ x) = j₂ (q₂ x) at hx
  change q₁ x = 0 ↔ q₂ x = 0
  constructor
  · intro h
    apply hj₂
    simpa only [h, map_zero, smul_zero] using hx.symm
  · intro h
    apply hj₁
    have hz : c • j₁ (q₁ x) = 0 := by
      simpa only [h, map_zero] using hx
    simpa only [map_zero] using (smul_eq_zero.mp hz).resolve_left hc0

/-- An irreducible quotient is the strong irreducible head if every
irreducible quotient embeds into a common representation and the Hom space
to that representation is one-dimensional. -/
theorem isIrreducibleHead_of_finrank_one
    {W : Type uV} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G W}
    (hdim : Module.finrank ℂ (ρ.IntertwiningMap β) = 1)
    (hembed : ∀ (W' : Type uV) [AddCommGroup W'] [Module ℂ W']
      (π' : Representation ℂ G W'), IsIrreducibleQuotient ρ π' →
        ∃ j : π'.IntertwiningMap β, Function.Injective j)
    (hπ : IsIrreducibleQuotient ρ π) :
    IsIrreducibleHead ρ π := by
  obtain ⟨hirr, q, hq⟩ := hπ
  obtain ⟨j, hj⟩ := hembed W π ⟨hirr, q, hq⟩
  have hq0 : q ≠ 0 := by
    let := hirr
    let : Nontrivial W := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.asModule
    intro h
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    obtain ⟨x, hx⟩ := hq w
    exact hw (by simpa only [h, Representation.IntertwiningMap.coe_zero,
      Pi.zero_apply] using hx.symm)
  refine ⟨hirr, q, hq, ?_⟩
  intro W' _ _ π' hirr' q' hq'
  obtain ⟨j', hj'⟩ := hembed W' π' ⟨hirr', q', hq'⟩
  have hq0' : q' ≠ 0 := by
    let := hirr'
    let : Nontrivial W' := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π'.asModule
    intro h
    obtain ⟨w, hw⟩ := exists_ne (0 : W')
    obtain ⟨x, hx⟩ := hq' w
    exact hw (by simpa only [h, Representation.IntertwiningMap.coe_zero,
      Pi.zero_apply] using hx.symm)
  exact quotientKernels_eq_of_finrank_one hdim q' q hq0' hq0 j' j hj' hj

section Smooth

variable [TopologicalSpace G]

/-- It suffices to establish the embedding property for bundled smooth
irreducible quotients: every algebraic quotient tested by the strong-head
relation inherits smoothness from the source. -/
theorem smooth_isIrreducibleHead_of_finrank_one
    (A : SmoothRep.{0, uG, uV} ℂ G) (C : SmoothRep.{0, uG, uB} ℂ G)
    (hdim : Module.finrank ℂ (A.representation.IntertwiningMap C.representation) = 1)
    (hembed : ∀ P : SmoothRep.{0, uG, uV} ℂ G,
      IsIrreducibleQuotient A.representation P.representation →
        ∃ j : P.representation.IntertwiningMap C.representation, Function.Injective j)
    (P : SmoothRep.{0, uG, uV} ℂ G)
    (hP : IsIrreducibleQuotient A.representation P.representation) :
    IsIrreducibleHead A.representation P.representation := by
  apply isIrreducibleHead_of_finrank_one hdim ?_ hP
  intro W _ _ π hπ
  obtain ⟨hirr, q, hq⟩ := hπ
  let Q : SmoothRep.{0, uG, uV} ℂ G :=
    SmoothRep.of π (isSmooth_of_surjective q hq A.isSmooth)
  exact hembed Q ⟨hirr, q, hq⟩

/-- Choose a smooth strong irreducible head from the one-dimensional Hom
criterion and existence of an irreducible quotient. -/
def smoothHeadOfFinrankOne
    (A : SmoothRep.{0, uG, uV} ℂ G) (C : SmoothRep.{0, uG, uB} ℂ G)
    (hdim : Module.finrank ℂ (A.representation.IntertwiningMap C.representation) = 1)
    (hembed : ∀ P : SmoothRep.{0, uG, uV} ℂ G,
      IsIrreducibleQuotient A.representation P.representation →
        ∃ j : P.representation.IntertwiningMap C.representation, Function.Injective j)
    (hexists : ∃ P : SmoothRep.{0, uG, uV} ℂ G,
      IsIrreducibleQuotient A.representation P.representation) :
    {P : SmoothRep.{0, uG, uV} ℂ G //
      IsIrreducibleHead A.representation P.representation} :=
  ⟨hexists.choose,
    smooth_isIrreducibleHead_of_finrank_one A C hdim hembed _ hexists.choose_spec⟩

end Smooth

end Langlands.Classification
