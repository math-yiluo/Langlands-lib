import Langlands.Representation.Geometric.RepresentedParabolicSupportFiltration

/-! # Bruhat relation, support subspaces and `PQ`-regularity (Renard VII.3.1–VII.3.3)

For two represented parabolics `P = MN` and `Q = MU` with the same Levi scheme `M`, this
module defines the Bruhat relation on the actual double cosets `P(F) \ G(F) / Q(F)`, the four
support subspaces of `i_P^G(W)` of Renard VII.3.2 and their images in `r_Q^G i_P^G(W)`, the
ideals `I_σ`, `I^{PQ}_σ` and `I^{Q,w}_σ` of the group algebra `ℂ[A(F)]` for a homomorphism
`a : A → M` (Renard: the split component `A_M`), and `PQ`-regularity. The definitions do not
need the two embeddings of `M` in `G` to agree. Nothing about these objects is asserted beyond
the structural facts used to build them.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Geometric

universe uR uG uV

section Bruhat

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Renard's Bruhat relation `w ≤_{PQ} w'` on `P \ G / Q` (VII.3.1): the actual double coset
`P w Q` is contained in the closure of `P w' Q`. -/
def BruhatLE (P Q : Subgroup G) (w w' : DoubleCoset.Quotient (P : Set G) Q) : Prop :=
  DoubleCoset.quotToDoubleCoset P Q w ⊆ closure (DoubleCoset.quotToDoubleCoset P Q w')

/-- The strict Bruhat relation `w <_{PQ} w'`: `w ≤_{PQ} w'` and `w ≠ w'`. -/
def BruhatLT (P Q : Subgroup G) (w w' : DoubleCoset.Quotient (P : Set G) Q) : Prop :=
  BruhatLE P Q w w' ∧ w ≠ w'

theorem bruhatLE_refl (P Q : Subgroup G) (w : DoubleCoset.Quotient (P : Set G) Q) :
    BruhatLE P Q w w :=
  subset_closure

theorem bruhatLE_trans {P Q : Subgroup G} {w w' w'' : DoubleCoset.Quotient (P : Set G) Q}
    (h : BruhatLE P Q w w') (h' : BruhatLE P Q w' w'') : BruhatLE P Q w w'' :=
  h.trans (closure_minimal h' isClosed_closure)

/-- A linear order on `P \ G / Q` refines the Bruhat relation, as Renard's `⪯` does. -/
def IsBruhatRefinement (P Q : Subgroup G) (o : LinearOrder (DoubleCoset.Quotient (P : Set G) Q)) :
    Prop :=
  ∀ w w', BruhatLE P Q w w' → o.le w w'

end Bruhat

section Invariance

variable {G : Type uG} [Group G]

/-- A union of actual double cosets is right-invariant. -/
theorem preimage_mk_mul_mem (P Q : Subgroup G) (T : Set (DoubleCoset.Quotient (P : Set G) Q))
    (x : Q) (g : G) (hg : g ∈ DoubleCoset.mk P Q ⁻¹' T) :
    g * (x : G) ∈ DoubleCoset.mk P Q ⁻¹' T := by
  simpa only [Set.mem_preimage, DoubleCoset.mk_mul_mem] using hg

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The closure of a double coset is right-invariant. -/
theorem closure_doubleCoset_mul_mem (P Q : Subgroup G) (w : DoubleCoset.Quotient (P : Set G) Q)
    (x : Q) (g : G) (hg : g ∈ closure (DoubleCoset.quotToDoubleCoset P Q w)) :
    g * (x : G) ∈ closure (DoubleCoset.quotToDoubleCoset P Q w) := by
  refine map_mem_closure (f := fun y => y * (x : G)) (continuous_mul_const (x : G)) hg ?_
  intro y hy
  rw [DoubleCoset.mem_quotToDoubleCoset_iff] at hy ⊢
  rw [DoubleCoset.mk_mul_mem, hy]

/-- The boundary `closure (P w Q) \ P w Q` of a double coset is right-invariant. -/
theorem boundary_doubleCoset_mul_mem (P Q : Subgroup G) (w : DoubleCoset.Quotient (P : Set G) Q)
    (x : Q) (g : G)
    (hg : g ∈ closure (DoubleCoset.quotToDoubleCoset P Q w) \
      DoubleCoset.quotToDoubleCoset P Q w) :
    g * (x : G) ∈ closure (DoubleCoset.quotToDoubleCoset P Q w) \
      DoubleCoset.quotToDoubleCoset P Q w := by
  refine ⟨closure_doubleCoset_mul_mem P Q w x g hg.1, ?_⟩
  intro hgx
  apply hg.2
  rw [DoubleCoset.mem_quotToDoubleCoset_iff] at hgx ⊢
  rwa [DoubleCoset.mk_mul_mem] at hgx

end Invariance

section Vanishing

variable {R : Type uR} [CommRing R]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Smoothly induced functions vanishing on an actual right-`Q`-invariant subset `Z` of `G`:
the published support subfunctor for the complement of the image of `Z` in `P \ G`. -/
def rawSmoothVanishingSubfunctor (P Q : Subgroup G) (Z : Set G)
    (hZ : ∀ (x : Q) (g : G), g ∈ Z → g * (x : G) ∈ Z) :
    RepSubfunctor (rawRestrictedSmoothInduction.{uR, uG, uV} (R := R) P Q) :=
  rawSmoothSupportSubfunctor P Q (Induction.quotientMap P '' Z)ᶜ (by
    intro x c hc hxc
    obtain ⟨g, hg, hgc⟩ := hxc
    obtain ⟨y, rfl⟩ := Quotient.exists_rep c
    change Induction.quotientMap P g = Induction.quotientMap P (y * (x : G)) at hgc
    have h : (y * (x : G)) * g⁻¹ ∈ P :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact hgc)
    apply hc
    refine ⟨g * ((x : G))⁻¹, hZ x⁻¹ g hg, ?_⟩
    exact Quotient.sound (QuotientGroup.rightRel_apply.mpr
      (by simpa only [mul_inv_rev, inv_inv, mul_assoc] using h)))

/-- A function lies in the vanishing subfunctor exactly when it vanishes on `Z`. -/
theorem mem_rawSmoothVanishingSubfunctor_iff (P Q : Subgroup G) (Z : Set G)
    (hZ : ∀ (x : Q) (g : G), g ∈ Z → g * (x : G) ∈ Z) (A : Rep.{uV} R P)
    (f : Induction.SmoothFunctions P A.ρ) :
    f ∈ (rawSmoothVanishingSubfunctor.{uR, uG, uV} (R := R) P Q Z hZ).obj A ↔
      ∀ g ∈ Z, Induction.eval P A.ρ f g = 0 := by
  constructor
  · intro hf g hg
    by_contra hfg
    exact hf g hfg ⟨g, hg, rfl⟩
  · intro hf x hx hxZ
    obtain ⟨g, hg, hgx⟩ := hxZ
    have h : x * g⁻¹ ∈ P :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact hgx)
    apply hx
    have hcov := f.1.2 ⟨x * g⁻¹, h⟩ g
    change Induction.eval P A.ρ f (x * g⁻¹ * g) = A.ρ ⟨x * g⁻¹, h⟩ (Induction.eval P A.ρ f g)
      at hcov
    rw [inv_mul_cancel_right, hf g hg, map_zero] at hcov
    exact hcov

end Vanishing

end Langlands.Geometric

namespace Langlands

universe uH uB uV

/-- The kernel in the group algebra `ℂ[B]` of the linear extension of `ρ ∘ φ`. -/
def groupAlgebraKernel {H : Type uH} {B : Type uB} [Monoid H] [Monoid B]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) (φ : B →* H) :
    Ideal (MonoidAlgebra ℂ B) :=
  RingHom.ker (Representation.asAlgebraHom (ρ.comp φ))

theorem mem_groupAlgebraKernel_iff {H : Type uH} {B : Type uB} [Monoid H] [Monoid B]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) (φ : B →* H)
    (x : MonoidAlgebra ℂ B) :
    x ∈ groupAlgebraKernel ρ φ ↔ Representation.asAlgebraHom (ρ.comp φ) x = 0 :=
  RingHom.mem_ker

end Langlands

universe u v

open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance regularityAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q U : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
  (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
  (hq : IsParabolicSubgroup q) (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
  (hlQ : IsRationalLeviSubgroup lQ) (hmulQ : IsIso (subgroupMultiplication lQ rQ))

/-- The actual double cosets `P(F) \ G(F) / Q(F)`. -/
abbrev parabolicDoubleCosets :=
  DoubleCoset.Quotient (pointImage p : Set (rationalPoints G)) (pointImage q)

/-- Renard's `1̄`, the double coset `P(F) Q(F)` of the identity. -/
abbrev identityParabolicDoubleCoset : parabolicDoubleCosets p q :=
  DoubleCoset.mk (pointImage p) (pointImage q) 1

/-- Functions of `i_P^G(W)`, restricted to `Q(F)`, vanishing on an actual right-`Q(F)`-invariant
subset `Z` of `G(F)`. -/
def leviVanishingSubfunctor (Z : Set (rationalPoints G))
    (hZ : ∀ (x : pointImage q) (g : rationalPoints G), g ∈ Z → g * (x : rationalPoints G) ∈ Z) :
    letI := leviPointTopology l hl
    RepSubfunctor
      (leviInductionFunctor.{u, v} p l r hp hr hl hmul ⋙ SmoothRep.toRep ⋙
        Rep.resFunctor (pointImage q).subtype) := by
  letI := leviPointTopology l hl
  exact (Geometric.rawSmoothVanishingSubfunctor.{0, u, v} (R := ℂ) (pointImage p) (pointImage q)
    Z hZ).precomp (leviInducingFunctor p l r hp hr hl hmul)

/-- Renard's `F̃^{⪯w}_{PQ}`: functions whose support misses `⋃_{w' ⪯ w} P w' Q`, for a linear
order `o` on `P(F) \ G(F) / Q(F)`. -/
def initialVanishingSubfunctor (o : LinearOrder (parabolicDoubleCosets p q))
    (w : parabolicDoubleCosets p q) :
    letI := leviPointTopology l hl
    RepSubfunctor
      (leviInductionFunctor.{u, v} p l r hp hr hl hmul ⋙ SmoothRep.toRep ⋙
        Rep.resFunctor (pointImage q).subtype) :=
  leviVanishingSubfunctor p l r hp hr hl hmul q
    (DoubleCoset.mk (pointImage p) (pointImage q) ⁻¹' {w' | o.le w' w})
    (Geometric.preimage_mk_mul_mem _ _ _)

/-- Renard's `F̃^{≺w}_{PQ}`: functions whose support misses `⋃_{w' ≺ w} P w' Q`. -/
def strictInitialVanishingSubfunctor (o : LinearOrder (parabolicDoubleCosets p q))
    (w : parabolicDoubleCosets p q) :
    letI := leviPointTopology l hl
    RepSubfunctor
      (leviInductionFunctor.{u, v} p l r hp hr hl hmul ⋙ SmoothRep.toRep ⋙
        Rep.resFunctor (pointImage q).subtype) :=
  leviVanishingSubfunctor p l r hp hr hl hmul q
    (DoubleCoset.mk (pointImage p) (pointImage q) ⁻¹' {w' | o.lt w' w})
    (Geometric.preimage_mk_mul_mem _ _ _)

/-- Renard's `F̃^{<w}_{PQ}`: functions with `Supp f ∩ closure (P w Q) ⊆ P w Q`, that is,
vanishing on `closure (P w Q) \ P w Q`. -/
def boundaryVanishingSubfunctor (w : parabolicDoubleCosets p q) :
    letI := leviPointTopology l hl
    RepSubfunctor
      (leviInductionFunctor.{u, v} p l r hp hr hl hmul ⋙ SmoothRep.toRep ⋙
        Rep.resFunctor (pointImage q).subtype) :=
  leviVanishingSubfunctor p l r hp hr hl hmul q
    (closure (DoubleCoset.quotToDoubleCoset (pointImage p) (pointImage q) w) \
      DoubleCoset.quotToDoubleCoset (pointImage p) (pointImage q) w)
    (Geometric.boundary_doubleCoset_mul_mem _ _ w)

/-- Renard's `F̃^{≤w}_{PQ}`: functions with `Supp f ∩ closure (P w Q) = ∅`. -/
def closureVanishingSubfunctor (w : parabolicDoubleCosets p q) :
    letI := leviPointTopology l hl
    RepSubfunctor
      (leviInductionFunctor.{u, v} p l r hp hr hl hmul ⋙ SmoothRep.toRep ⋙
        Rep.resFunctor (pointImage q).subtype) :=
  leviVanishingSubfunctor p l r hp hr hl hmul q
    (closure (DoubleCoset.quotToDoubleCoset (pointImage p) (pointImage q) w))
    (Geometric.closure_doubleCoset_mul_mem _ _ w)

/-- Renard's `F^{⪯w}_{PQ}`: the image of `F̃^{⪯w}_{PQ}` in `r_Q^G i_P^G`. -/
def initialSupportImage (o : LinearOrder (parabolicDoubleCosets p q))
    (w : parabolicDoubleCosets p q) :
    letI := leviPointTopology l hl
    RepSubfunctor
      (leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ) :=
  leviJacquetImageSubfunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
    (initialVanishingSubfunctor p l r hp hr hl hmul q o w)

/-- Renard's `F^{≺w}_{PQ}`: the image of `F̃^{≺w}_{PQ}` in `r_Q^G i_P^G`. -/
def strictInitialSupportImage (o : LinearOrder (parabolicDoubleCosets p q))
    (w : parabolicDoubleCosets p q) :
    letI := leviPointTopology l hl
    RepSubfunctor
      (leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ) :=
  leviJacquetImageSubfunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
    (strictInitialVanishingSubfunctor p l r hp hr hl hmul q o w)

/-- Renard's `F^{<w}_{PQ}`: the image of `F̃^{<w}_{PQ}` in `r_Q^G i_P^G`. -/
def boundarySupportImage (w : parabolicDoubleCosets p q) :
    letI := leviPointTopology l hl
    RepSubfunctor
      (leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ) :=
  leviJacquetImageSubfunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
    (boundaryVanishingSubfunctor p l r hp hr hl hmul q w)

/-- Renard's `F^{≤w}_{PQ}`: the image of `F̃^{≤w}_{PQ}` in `r_Q^G i_P^G`. -/
def closureSupportImage (w : parabolicDoubleCosets p q) :
    letI := leviPointTopology l hl
    RepSubfunctor
      (leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ) :=
  leviJacquetImageSubfunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
    (closureVanishingSubfunctor p l r hp hr hl hmul q w)

variable {A : CommGroupScheme (Spec (CommRingCat.of k))} (a : A.toGrp ⟶ M)

/-- Renard's `I_σ = ker σ|ℂ[A_M]`: the kernel in `ℂ[A(F)]` of the action of `A(F)` on `σ`
through `a`. Renard takes for `a` the split component `A_M` of `M`. -/
def splitComponentKernel
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    Ideal (MonoidAlgebra ℂ (rationalPoints A.toGrp)) :=
  letI := leviPointTopology l hl
  groupAlgebraKernel σ.representation (rationalPoints.map a)

/-- Renard's `I^{PQ}_σ`: the kernel in `ℂ[A(F)]` of the action through `a` on
`(r_Q^G ∘ i_P^G / F^{<1̄}_{PQ})(σ)`, a representation of `M(F)` as the Levi of `Q`. -/
def pqRegularityKernel
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    Ideal (MonoidAlgebra ℂ (rationalPoints A.toGrp)) :=
  letI := leviPointTopology l hl
  let S := ((boundarySupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
    (identityParabolicDoubleCoset p q)).obj σ)
  groupAlgebraKernel
    (((leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ).obj
      σ).ρ.quotient S.toSubmodule (fun g _ hv => S.apply_mem_toSubmodule g hv))
    (rationalPoints.map a)

/-- Renard's `PQ`-regularity, condition (i) of the Lemma in VII.3.3:
`I_σ + I^{PQ}_σ = ℂ[A(F)]`. -/
def IsPQRegular
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) : Prop :=
  splitComponentKernel l hl a σ ⊔
    pqRegularityKernel p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ = ⊤

variable {p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ} in
/-- Renard's `I^{Q,w̄}_σ`, read on the full graded piece `i^M_{Q'} ∘ w ∘ r^M_{P'}(σ)` of the
geometric lemma at an intersection datum `D` for a representative `z` of `w̄`: the kernel in
`ℂ[A(F)]` of the action through `a` on that piece. Renard defines `I^{Q,w̄}_σ` on
`w ∘ r^M_{M∩w·Q}(σ)`; his proof of the VII.3.3 Lemma identifies the two kernels by
faithfulness of parabolic induction, which is not proved here. -/
def pieceSplitComponentKernel {z : rationalPoints G}
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    Ideal (MonoidAlgebra ℂ (rationalPoints A.toGrp)) :=
  letI := leviPointTopology l hl
  groupAlgebraKernel (D.pieceFunctor.obj σ).ρ (rationalPoints.map a)

end Langlands.Aubert.General.RepresentedParabolic
