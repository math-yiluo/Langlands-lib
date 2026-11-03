import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Torus.WeightDecomposition
import Langlands.GroupScheme.Torus.Diagonalizable
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Noetherian.Orzech

/-! # Monomorphisms of actual finite split tori -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.splitTorus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k] (I J : Type u) [Finite I] [Finite J]
local notation "S" => Spec (CommRingCat.of k)
local notation "TI" => commGroupScheme S I
local notation "TJ" => commGroupScheme S J

/-- Pullback of actual characters in integral coordinates. -/
def characterMap (f : splitTorus S I ⟶ splitTorus S J) : (J → ℤ) →ₗ[ℤ] (I → ℤ) :=
  (((characterLatticeEquiv k I).toAddMonoidHom.comp
    { toFun := fun χ : characterLattice TJ => (Additive.ofMul f : TI ⟶ TJ) ≫ χ
      map_zero' := by simp
      map_add' := fun χ ψ => Preadditive.comp_add TI TJ (Gm S) (Additive.ofMul f) χ ψ }).comp
    (characterLatticeEquiv k J).symm.toAddMonoidHom).toIntLinearMap

@[simp] theorem characterMap_equiv (f : splitTorus S I ⟶ splitTorus S J)
    (χ : characterLattice TJ) :
    characterMap I J f (characterLatticeEquiv k J χ) =
      characterLatticeEquiv k I ((Additive.ofMul f : TI ⟶ TJ) ≫ χ) := by
  simp [characterMap]

section MonomialPoints

variable [Fintype I] [DecidableEq I]
variable (Q : Type u) [AddCommGroup Q]

/-- Exponent vectors give the actual invertible monomials in a group algebra. -/
def monomialUnit : Multiplicative Q →* (AddMonoidAlgebra k Q)ˣ :=
  Diagonalizable.monomialUnits (CommRingCat.of k) Q

/-- The monomial point associated to a homomorphism from the character lattice. -/
def monomialPoint (q : (I → ℤ) →ₗ[ℤ] Q) :
    Lie.AffinePoints (splitTorus S I) (AddMonoidAlgebra k Q) :=
  (algebraPointsEquiv I _).symm
    (fun i => monomialUnit Q (Multiplicative.ofAdd (q (Pi.single i 1))))

/-- Evaluation of a character at a monomial point is the corresponding monomial. -/
theorem characterValue_monomialPoint (q : (I → ℤ) →ₗ[ℤ] Q) (m : I → ℤ) :
    Lie.characterValue ((characterLatticeEquiv k I).symm m) (monomialPoint I Q q) =
      monomialUnit Q (Multiplicative.ofAdd (q m)) := by
  rw [characterValue_characterLatticeEquiv_symm]
  let h : (I → ℤ) →+ Additive (AddMonoidAlgebra k Q)ˣ :=
    { toFun := fun m => Additive.ofMul (monomialUnit Q (Multiplicative.ofAdd (q m)))
      map_zero' := by simp
      map_add' := fun m n => by
        apply Additive.toMul.injective
        change monomialUnit Q (Multiplicative.ofAdd (q (m + n))) = _
        rw [map_add]
        exact map_mul _ _ _ }
  have hm : (∑ j : I, m j • Pi.single j (1 : ℤ)) = m := by
    ext j
    simp [Pi.single_apply]
  have hh := congrArg Additive.toMul (map_sum h
    (fun j => m j • Pi.single j (1 : ℤ)) Finset.univ)
  rw [hm] at hh
  simp only [map_zsmul] at hh
  simpa [h, exponentValue, monomialPoint] using hh.symm

end MonomialPoints

/-- Scheme-theoretic injectivity forces surjectivity on integral characters.
The test algebra is the group algebra of the character cokernel. -/
theorem characterMap_surjective (f : splitTorus S I ⟶ splitTorus S J)
    [Mono f.hom.hom] : Function.Surjective (characterMap I J f) := by
  classical
  let := Fintype.ofFinite I
  let := Fintype.ofFinite J
  let g := characterMap I J f
  let Q := (I → ℤ) ⧸ LinearMap.range g
  let q : (I → ℤ) →ₗ[ℤ] Q := (LinearMap.range g).mkQ
  let x := monomialPoint (k := k) I Q q
  have hx : x ≫ f.hom.hom = 1 := by
    apply (algebraPointsEquiv J (AddMonoidAlgebra k Q)).injective
    rw [map_one]
    funext j
    change Lie.characterValue ((Additive.ofMul f : TI ⟶ TJ) ≫ proj S J j) x = 1
    rw [← (characterLatticeEquiv k I).symm_apply_apply
      ((Additive.ofMul f : TI ⟶ TJ) ≫ proj S J j), characterValue_monomialPoint]
    have hq : q (characterLatticeEquiv k I ((Additive.ofMul f : TI ⟶ TJ) ≫ proj S J j)) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero (LinearMap.range g)).mpr
      exact ⟨characterLatticeEquiv k J (proj S J j), characterMap_equiv I J f _⟩
    rw [hq]
    exact map_one _
  have hx1 : x = 1 := (cancel_mono f.hom.hom).mp (hx.trans (MonObj.one_comp _).symm)
  have hq_single (i : I) : q (Pi.single i 1) = 0 := by
    have h := congrFun (congrArg (algebraPointsEquiv I (AddMonoidAlgebra k Q)) hx1) i
    change (algebraPointsEquiv I _)
      ((algebraPointsEquiv I _).symm _) i = (algebraPointsEquiv I _) 1 i at h
    rw [MulEquiv.apply_symm_apply, map_one] at h
    have hv := congrArg Units.val h
    change AddMonoidAlgebra.single (q (Pi.single i 1)) (1 : k) =
      AddMonoidAlgebra.single (0 : Q) (1 : k) at hv
    exact AddMonoidAlgebra.single_left_injective (one_ne_zero : (1 : k) ≠ 0) hv
  intro m
  apply (Submodule.Quotient.mk_eq_zero (LinearMap.range g)).mp
  change q m = 0
  have hm : (∑ j : I, m j • Pi.single j (1 : ℤ)) = m := by
    ext j
    simp [Pi.single_apply]
  rw [← hm, map_sum]
  simp only [map_smul, hq_single, smul_zero, Finset.sum_const_zero]

/-- At equal finite rank the surjective character map is also injective. -/
theorem characterMap_injective_of_card_eq (f : splitTorus S I ⟶ splitTorus S J)
    [Mono f.hom.hom] (hcard : Nat.card I = Nat.card J) :
    Function.Injective (characterMap I J f) := by
  classical
  let := Fintype.ofFinite I
  let := Fintype.ofFinite J
  let e : I ≃ J := Fintype.equivOfCardEq (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let r : (J → ℤ) →ₗ[ℤ] (I → ℤ) :=
    { toFun := fun x i => x (e i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hr : Function.Injective r := by
    intro x y h
    funext j
    obtain ⟨i, rfl⟩ := e.surjective j
    exact congrFun h i
  exact IsNoetherian.injective_of_surjective_of_injective r (characterMap I J f) hr
    (characterMap_surjective I J f)

private theorem commHom_ext_proj {P : CommGroupScheme S} {f g : P ⟶ TJ}
    (h : ∀ j, f ≫ proj S J j = g ≫ proj S J j) : f = g := by
  apply Additive.toMul.injective
  apply Pi.hom_ext
  intro j
  exact congrArg Additive.toMul (h j)

/-- An equal-rank monomorphism between actual finite split tori is an isomorphism. -/
theorem isIso_of_mono_of_card_eq (f : splitTorus S I ⟶ splitTorus S J)
    [Mono f.hom.hom] (hcard : Nat.card I = Nat.card J) : IsIso f := by
  classical
  let := Fintype.ofFinite I
  let := Fintype.ofFinite J
  let a : TI ⟶ TJ := Additive.ofMul f
  have hc : ∀ i, ∃ χ : characterLattice TJ,
      a ≫ χ = proj S I i := by
    intro i
    obtain ⟨m, hm⟩ := characterMap_surjective I J f (characterLatticeEquiv k I (proj S I i))
    refine ⟨(characterLatticeEquiv k J).symm m, (characterLatticeEquiv k I).injective ?_⟩
    exact hm
  choose ψ hψ using hc
  let g : TJ ⟶ TI := ∑ i, ψ i ≫ single S I i
  have hfg : a ≫ g = 𝟙 TI := by
    dsimp only [g]
    rw [Preadditive.comp_sum]
    simp_rw [← Category.assoc, hψ]
    exact sum_proj_comp_single S I
  have hgf : g ≫ a = 𝟙 TJ := by
    apply commHom_ext_proj J
    intro j
    apply (characterLatticeEquiv k J).injective
    apply characterMap_injective_of_card_eq I J f hcard
    rw [characterMap_equiv, characterMap_equiv]
    change (characterLatticeEquiv k I) (a ≫ ((g ≫ a) ≫ proj S J j)) =
      (characterLatticeEquiv k I) (a ≫ ((𝟙 TJ) ≫ proj S J j))
    apply congrArg (characterLatticeEquiv k I)
    calc
      a ≫ ((g ≫ a) ≫ proj S J j) = (a ≫ g) ≫ (a ≫ proj S J j) := by
        simp only [Category.assoc]
      _ = a ≫ ((𝟙 TJ) ≫ proj S J j) := by rw [hfg]; simp
  exact ⟨⟨g.toMul, congrArg Additive.toMul hfg, congrArg Additive.toMul hgf⟩⟩

end Langlands.GroupScheme.splitTorus
