import Langlands.GroupScheme.Torus.DiagonalizablePower
import Langlands.GroupScheme.Torus.DiagonalizableDecomposition
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Dynamic.Uniqueness
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.GroupTheory.Exponent

/-! # Power factorization and full finite quotient of a diagonalizable group -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj DirectSum

namespace Langlands.GroupScheme
namespace Diagonalizable

section Split

variable (R : CommRingCat.{u}) {Λ I A : Type u}
  [AddCommGroup Λ] [AddCommGroup A]
  (e : Λ ≃+ (I → ℤ) × A)

/-- The torus inclusion induced by projection onto the free character factor. -/
def freeInclusion : (groupScheme R (I → ℤ)).toGrp ⟶ (groupScheme R Λ).toGrp :=
  restrictMap R ((AddMonoidHom.fst (I → ℤ) A).comp e.toAddMonoidHom)

/-- The finite-factor quotient induced by inclusion of its character factor. -/
def finiteProjection : (groupScheme R Λ).toGrp ⟶ (groupScheme R A).toGrp :=
  restrictMap R (e.symm.toAddMonoidHom.comp (AddMonoidHom.inr (I → ℤ) A))

/-- The factor of the power map with target the free-character torus. -/
def powerToFree (n : ℕ) :
    (groupScheme R Λ).toGrp ⟶ (groupScheme R (I → ℤ)).toGrp :=
  restrictMap R (e.symm.toAddMonoidHom.comp
    ((AddMonoidHom.inl (I → ℤ) A).comp (n • AddMonoidHom.id (I → ℤ))))

theorem isClosedSubgroup_freeInclusion : IsClosedSubgroup (freeInclusion R e) := by
  apply isClosedImmersion_restrictMap
  intro l
  exact ⟨e.symm (l, 0), by simp⟩

theorem isSplitTorus_free [Fintype I] [DecidableEq I] : IsSplitTorus (groupScheme R (I → ℤ)).toGrp :=
  IsSplitTorus.of_iso (splitIso R (AddEquiv.refl (I → ℤ)))
    (isSplitTorus_splitTorus I)

theorem powerToFree_comp_freeInclusion (n : ℕ) (hn : ∀ a : A, n • a = 0) :
    powerToFree R e n ≫ freeInclusion R e =
      powerHom (groupScheme R Λ).toGrp n := by
  rw [powerToFree, freeInclusion, restrictMap_comp, ← restrictMap_nsmul_id]
  congr 1
  apply AddMonoidHom.ext
  intro a
  change e.symm (n • (e a).1, 0) = n • a
  apply e.injective
  rw [AddEquiv.apply_symm_apply, map_nsmul]
  exact Prod.ext rfl (hn (e a).2).symm

theorem flat_surjective_powerToFree [Nontrivial R] (n : ℕ) (hn : n ≠ 0) :
    Flat (powerToFree R e n).hom.hom.left ∧
      Surjective (powerToFree R e n).hom.hom.left := by
  apply flat_and_surjective_restrictMap
  change Function.Injective (fun x : I → ℤ => e.symm (n • x, 0))
  intro x y h
  exact nsmul_right_injective hn (congrArg Prod.fst (e.symm.injective h))

theorem flat_surjective_finiteProjection [Nontrivial R] :
    Flat (finiteProjection R e).hom.hom.left ∧
      Surjective (finiteProjection R e).hom.hom.left := by
  apply flat_and_surjective_restrictMap
  exact e.symm.injective.comp (fun x y h => congrArg Prod.snd h)

/-- The free-target factor is schematically dominant, including inseparable powers. -/
theorem dominant_powerToFree (n : ℕ) (hn : n ≠ 0) :
    IsSchemeTheoreticallyDominant (powerToFree R e n).hom.hom.left := by
  rw [powerToFree, restrictMap_left]
  apply isSchemeTheoreticallyDominant_specMap
  apply AddMonoidAlgebra.mapDomain_injective
  change Function.Injective (fun x : I → ℤ => e.symm (n • x, 0))
  intro x y h
  exact nsmul_right_injective hn (congrArg Prod.fst (e.symm.injective h))

/-- The full kernel of the finite-factor projection is the free-factor torus. -/
theorem kernel_finiteProjection :
    SubgroupFunctor.range (kernelι (finiteProjection R e)) =
      SubgroupFunctor.range (freeInclusion R e) := by
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro x
  rw [mem_range_kernelι_iff]
  constructor
  · intro hx
    let χ := characterPointsEquiv R Λ U x
    let χL := χ.comp (AddMonoidHom.toMultiplicative
      (e.symm.toAddMonoidHom.comp (AddMonoidHom.inl (I → ℤ) A)))
    let t := (characterPointsEquiv R (I → ℤ) U).symm χL
    have hker (a : A) : χ (.ofAdd (e.symm (0, a))) = 1 := by
      calc
        _ = characterPointsEquiv R A U
            (x ≫ (finiteProjection R e).hom.hom) (.ofAdd a) :=
          (pointsEquiv_restrictMap R
            (e.symm.toAddMonoidHom.comp (AddMonoidHom.inr (I → ℤ) A)) x a).symm
        _ = 1 := by rw [hx, map_one]; rfl
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨t, ?_⟩
    apply (characterPointsEquiv R Λ U).injective
    apply MonoidHom.ext
    intro a
    change characterPointsEquiv R Λ U
        (t ≫ (freeInclusion R e).hom.hom) (.ofAdd a.toAdd) = χ a
    have heval : characterPointsEquiv R Λ U
        (t ≫ (freeInclusion R e).hom.hom) (.ofAdd a.toAdd) =
        characterPointsEquiv R (I → ℤ) U t (.ofAdd (e a.toAdd).1) :=
      pointsEquiv_restrictMap R
        ((AddMonoidHom.fst (I → ℤ) A).comp e.toAddMonoidHom) t a.toAdd
    rw [heval]
    change characterPointsEquiv R (I → ℤ) U
        ((characterPointsEquiv R (I → ℤ) U).symm χL) (.ofAdd (e a.toAdd).1) = χ a
    rw [MulEquiv.apply_symm_apply]
    change χ (.ofAdd (e.symm ((e a.toAdd).1, 0))) = χ a
    have ha : a = Multiplicative.ofAdd (e.symm ((e a.toAdd).1, 0)) *
        .ofAdd (e.symm (0, (e a.toAdd).2)) := by
      change a.toAdd = e.symm ((e a.toAdd).1, 0) + e.symm (0, (e a.toAdd).2)
      rw [← map_add]
      simp
    conv_rhs => rw [ha, map_mul, hker, mul_one]
  · intro hx
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    apply (characterPointsEquiv R A U).injective
    apply MonoidHom.ext
    intro a
    change characterPointsEquiv R A U
      ((t ≫ (freeInclusion R e).hom.hom) ≫ (finiteProjection R e).hom.hom)
        (.ofAdd a.toAdd) = _
    have hproj : characterPointsEquiv R A U
        ((t ≫ (freeInclusion R e).hom.hom) ≫ (finiteProjection R e).hom.hom)
          (.ofAdd a.toAdd) =
        characterPointsEquiv R Λ U (t ≫ (freeInclusion R e).hom.hom)
          (.ofAdd (e.symm (0, a.toAdd))) :=
      pointsEquiv_restrictMap R
        (e.symm.toAddMonoidHom.comp (AddMonoidHom.inr (I → ℤ) A))
        (t ≫ (freeInclusion R e).hom.hom) a.toAdd
    have hinc : characterPointsEquiv R Λ U (t ≫ (freeInclusion R e).hom.hom)
        (.ofAdd (e.symm (0, a.toAdd))) =
        characterPointsEquiv R (I → ℤ) U t (.ofAdd (e (e.symm (0, a.toAdd))).1) :=
      pointsEquiv_restrictMap R
        ((AddMonoidHom.fst (I → ℤ) A).comp e.toAddMonoidHom) t (e.symm (0, a.toAdd))
    rw [hproj, hinc]
    simp


/-- Over a Noetherian ring, the finite-factor map is the actual fppf quotient. -/
theorem isFppfQuotient_finiteProjection [Nontrivial R] [IsNoetherianRing R]
    [AddGroup.FG Λ] [AddGroup.FG A] :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (freeInclusion R e))
      (finiteProjection R e) := by
  obtain ⟨hf, hs⟩ := flat_surjective_finiteProjection R e
  have : IsLocallyNoetherian (groupScheme R A).X.left :=
    LocallyOfFiniteType.isLocallyNoetherian (groupScheme R A).X.hom
  have : LocallyOfFiniteType
      ((finiteProjection R e).hom.hom.left ≫ (groupScheme R A).X.hom) := by
    rw [Over.w]
    infer_instance
  have : LocallyOfFiniteType (finiteProjection R e).hom.hom.left :=
    locallyOfFiniteType_of_comp _ (groupScheme R A).X.hom
  exact ⟨hf, hs, inferInstance, kernel_finiteProjection R e⟩


end Split
/-- A free/finite character decomposition in the original universe. -/
theorem exists_freeFiniteEquiv (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ] :
    ∃ (I A : Type u) (_ : Fintype I) (_ : AddCommGroup A) (_ : Finite A),
      Nonempty (Λ ≃+ (I → ℤ) × A) := by
  classical
  obtain ⟨n, J, hJ, p, hp, e, ⟨b⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_zmod Λ
  have : ∀ i : J, NeZero (p i ^ e i) :=
    fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let A := ULift.{u} (⨁ i : J, ZMod (p i ^ e i))
  have : Finite (⨁ i : J, ZMod (p i ^ e i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  let c : (Fin n →₀ ℤ) ≃+ (ULift.{u} (Fin n) → ℤ) :=
    Finsupp.addEquivFunOnFinite.trans
      (AddEquiv.arrowCongr Equiv.ulift.symm (AddEquiv.refl ℤ))
  let b' : Λ ≃+ (ULift.{u} (Fin n) → ℤ) × A :=
    b.trans (c.prodCongr AddEquiv.ulift.symm)
  exact ⟨ULift.{u} (Fin n), A, inferInstance, inferInstance, inferInstance, ⟨b'⟩⟩

/-- A suitable actual power map has a closed split-torus dominant factorization,
with its full finite diagonalizable fppf quotient. -/
theorem exists_power_torus_finiteQuotient (k : Type u) [Field k]
    (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ] :
    ∃ (n : ℕ) (T : GroupScheme (Spec (CommRingCat.of k)))
      (j : T ⟶ (groupScheme (CommRingCat.of k) Λ).toGrp)
      (p : (groupScheme (CommRingCat.of k) Λ).toGrp ⟶ T),
      IsSplitTorus T ∧ IsClosedSubgroup j ∧
      IsSchemeTheoreticallyDominant p.hom.hom.left ∧
      p ≫ j = powerHom (groupScheme (CommRingCat.of k) Λ).toGrp n ∧
      ∃ (Q : GroupScheme (Spec (CommRingCat.of k)))
        (q : (groupScheme (CommRingCat.of k) Λ).toGrp ⟶ Q),
        IsFinite Q.X.hom ∧ RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q := by
  classical
  obtain ⟨I, A, hI, hA, hfin, ⟨e⟩⟩ := exists_freeFiniteEquiv Λ
  let R := CommRingCat.of k
  let n := AddMonoid.exponent A
  refine ⟨n, (groupScheme R (I → ℤ)).toGrp, freeInclusion R e, powerToFree R e n,
    isSplitTorus_free R, isClosedSubgroup_freeInclusion R e,
    dominant_powerToFree R e n AddMonoid.exponent_ne_zero_of_finite,
    powerToFree_comp_freeInclusion R e n (fun a => AddMonoid.exponent_nsmul_eq_zero a),
    (groupScheme R A).toGrp, finiteProjection R e, inferInstance,
    isFppfQuotient_finiteProjection R e⟩


end Diagonalizable
end Langlands.GroupScheme
