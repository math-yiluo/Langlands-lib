import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.RootFiniteness

/-! # Root-span kernels and restrictions of rational characters -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

section RationalCharacters

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Inner conjugation fixes every rational character, as a morphism of group schemes. -/
theorem rationalCharacters.comp_innerIso_hom (χ : rationalCharacters G)
    (n : Over.mk (𝟙 S) ⟶ G.X) :
    (G.innerIso n).hom ≫ χ.toMul = χ.toMul := by
  apply hom_ext_points
  intro U x
  rw [Grp.comp_hom_hom, ← Category.assoc, Langlands.GroupScheme.comp_innerIso_hom]
  simp only [MonObj.mul_comp, GrpObj.inv_comp]
  simp [mul_comm]

variable {T : CommGroupScheme S}

/-- Restriction of rational characters to the character lattice of a commutative group scheme. -/
def torusCharacterRestrict (i : T.toGrp ⟶ G) :
    rationalCharacters G →+ characterLattice T :=
  (rationalCharacters.equivCharacterLattice T).toAddMonoidHom.comp (characterRestrict i)

@[simp]
theorem groupHom_torusCharacterRestrict (i : T.toGrp ⟶ G) (χ : rationalCharacters G) :
    CommGroupScheme.groupHom (torusCharacterRestrict i χ) = i ≫ χ.toMul :=
  rfl

variable (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- The normalizer action fixes the restrictions of all rational characters of the group. -/
theorem weylAction_torusCharacterRestrict (n : normalizerPoints i) (χ : rationalCharacters G) :
    weylAction i n (torusCharacterRestrict i χ) = torusCharacterRestrict i χ := by
  have hn := (isNormalizingPoint_normalizingAut i n).inv
  change i ≫ (G.innerIso (n : Over.mk (𝟙 S) ⟶ G.X)⁻¹).hom =
    CommGroupScheme.groupHom (normalizingAut i n).inv ≫ i at hn
  rw [weylAction_apply]
  change Additive.ofMul
      (CommGroupScheme.groupHom (normalizingAut i n).inv ≫ i ≫ χ.toMul) =
    Additive.ofMul (i ≫ χ.toMul)
  congr 1
  rw [← Category.assoc, ← hn, Category.assoc, χ.comp_innerIso_hom]

end RationalCharacters

section RootSpan

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

/-- For a split torus, a normalizing point acts identically on the relative-root span
exactly when it fixes every actual relative root as a character. -/
theorem IsSplitTorus.relativeWeylAction_mk_eq_one_iff (hT : IsSplitTorus T.toGrp)
    (n : normalizerPoints i) :
    relativeWeylAction i (QuotientGroup.mk n) = 1 ↔
      ∀ α ∈ relativeRoots i, weylAction i n α = α := by
  constructor
  · intro hn α hα
    apply hT.character_toRat_injective
    have h := congrArg
      (fun e : relativeRootSpan i ≃ₗ[ℚ] relativeRootSpan i =>
        (e ⟨toRat α, toRat_mem_ratSpan hα⟩ : ℚ ⊗[ℤ] characterLattice T)) hn
    change toRat (weylAction i n α) = toRat α at h
    exact h
  · intro hn
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    change ratAut (weylAction i n) (x : ℚ ⊗[ℤ] characterLattice T) = x
    have hfix : ∀ (v : ℚ ⊗[ℤ] characterLattice T),
        v ∈ Submodule.span ℚ (toRat '' relativeRoots i) →
        ratAut (weylAction i n) v = v := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨α, hα, rfl⟩ := hv
        rw [ratAut_toRat, hn α hα]
      | zero => exact map_zero _
      | add x y hx hy ihx ihy => rw [map_add, ihx, ihy]
      | smul a x hx ih => rw [map_smul, ih]
    exact hfix x x.property

/-- A linear spanning criterion reducing the root-span kernel to the full-character kernel.
The spanning premise is a separate structural obligation. -/
theorem IsSplitTorus.weylAction_eq_one_of_fixed_roots
    (hT : IsSplitTorus T.toGrp)
    (hspan : Submodule.span ℚ
      (toRat '' (relativeRoots i ∪ Set.range (torusCharacterRestrict i))) = ⊤)
    (n : normalizerPoints i) (hn : ∀ α ∈ relativeRoots i, weylAction i n α = α) :
    weylAction i n = 1 := by
  have hrat : ratAut (weylAction i n) = 1 := by
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext_on hspan
    rintro _ ⟨χ, hχ, rfl⟩
    change toRat (weylAction i n χ) = toRat χ
    rcases hχ with hχ | ⟨ψ, rfl⟩
    · rw [hn χ hχ]
    · rw [weylAction_torusCharacterRestrict]
  apply LinearEquiv.ext
  intro χ
  apply hT.character_toRat_injective
  have h := congrArg
    (fun e : (ℚ ⊗[ℤ] characterLattice T) ≃ₗ[ℚ] (ℚ ⊗[ℤ] characterLattice T) =>
      e (toRat χ)) hrat
  exact h

/-- When roots and restricted group characters span the rational character lattice,
the root-span and full-character actions have the same kernel on normalizing points. -/
theorem IsSplitTorus.relativeWeylAction_mk_eq_one_iff_weylAction_eq_one
    (hT : IsSplitTorus T.toGrp)
    (hspan : Submodule.span ℚ
      (toRat '' (relativeRoots i ∪ Set.range (torusCharacterRestrict i))) = ⊤)
    (n : normalizerPoints i) :
    relativeWeylAction i (QuotientGroup.mk n) = 1 ↔ weylAction i n = 1 := by
  rw [hT.relativeWeylAction_mk_eq_one_iff i n]
  constructor
  · exact hT.weylAction_eq_one_of_fixed_roots i hspan n
  · intro hn α _
    rw [hn]
    rfl

end RootSpan

end Langlands.GroupScheme
