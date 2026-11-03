import Langlands.GroupScheme.Torus.Diagonalizable
import Langlands.GroupScheme.Rational.SplitTorusMonomorphism
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Diagonalizable

theorem incl_surjective {R : CommRingCat.{u}} {M N : Type u}
    [AddCommGroup M] [AddCommGroup N] (f : M →+ N) (hf : Function.Surjective f) :
    Function.Surjective (incl R f).hom := by
  intro x
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
  | single n r =>
      obtain ⟨m, rfl⟩ := hf n
      exact ⟨AddMonoidAlgebra.single m r, incl_single R f m r⟩

/-- A finite map of group algebras has a finite cokernel on exponent groups. -/
theorem finite_cokernel_of_incl_finite {k : Type u} [Field k] {M N : Type u}
    [AddCommGroup M] [AddCommGroup N] (f : M →+ N)
    (hf : (incl (CommRingCat.of k) f).hom.Finite) :
    Finite (N ⧸ f.range) := by
  let q : N →+ N ⧸ f.range := QuotientAddGroup.mk' f.range
  let α := (incl (CommRingCat.of k) f).hom
  let β := (incl (CommRingCat.of k) q).hom
  let ε : AddMonoidAlgebra k M →ₐ[k] k :=
    AddMonoidAlgebra.lift k k M 1
  let scalar : k →ₐ[k] AddMonoidAlgebra k (N ⧸ f.range) :=
    Algebra.ofId k _
  have hβ : β.Finite := AlgHom.Finite.of_surjective β
    (incl_surjective q (QuotientAddGroup.mk'_surjective _))
  have hcomp : β.comp α = scalar.comp ε := by
    apply AddMonoidAlgebra.algHom_ext
    · intro m
      simp only [AlgHom.coe_comp, Function.comp_apply]
      change (incl (CommRingCat.of k) q).hom
        ((incl (CommRingCat.of k) f).hom (AddMonoidAlgebra.single m 1)) = _
      rw [incl_single, incl_single]
      have hq : q (f m) = 0 := by
        exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨m, rfl⟩
      simp [hq, ε, scalar]
    · exact Subsingleton.elim _ _
  have hη : scalar.Finite := AlgHom.Finite.of_comp_finite (hcomp ▸ hβ.comp hf)
  have : Module.Finite k (AddMonoidAlgebra k (N ⧸ f.range)) :=
    RingHom.finite_algebraMap.mp hη
  exact Module.Finite.finite_basis (AddMonoidAlgebra.basis (N ⧸ f.range) k)

end Diagonalizable

namespace splitTorus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k] (I J : Type u)
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

local notation "R" => CommRingCat.of k
local notation "S" => Spec R
local notation "DI" => Diagonalizable.groupScheme R (I → ℤ)
local notation "DJ" => Diagonalizable.groupScheme R (J → ℤ)
local notation "eI" => Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ))
local notation "eJ" => Diagonalizable.splitIso R (AddEquiv.refl (J → ℤ))

theorem diagonalizable_splitIso_points (T : Over S) (x : T ⟶ (DI).X) :
    pointsEquiv I T (x ≫ (eI).hom.hom.hom) =
      Diagonalizable.splitPointsEquiv R (AddEquiv.refl (I → ℤ)) T x := by
  exact isoOfPointModels_hom _ _ _ _
    (Diagonalizable.splitPointsEquiv_naturality R (AddEquiv.refl (I → ℤ)))
    (fun a y => pointsEquiv_naturality I a y) T x

theorem characterLatticeEquiv_proj (j : J) :
    characterLatticeEquiv k J (proj S J j) = Pi.single j 1 := by
  apply (characterLatticeEquiv k J).symm.injective
  rw [AddEquiv.symm_apply_apply, characterLatticeEquiv_symm_eq]
  simp [Pi.single_apply]

/-- The diagonalizable map induced by the actual character pullback. -/
def diagonalizableMap (f : splitTorus S I ⟶ splitTorus S J) :
    (DI).toGrp ⟶ (DJ).toGrp :=
  Corepresented.groupSchemeMap (Diagonalizable.grpCorepresentation R (I → ℤ))
    (Diagonalizable.grpCorepresentation R (J → ℤ))
    (Diagonalizable.restrict R (characterMap I J f).toAddMonoidHom)

theorem diagonalizableMap_splitIso (f : splitTorus S I ⟶ splitTorus S J) :
    diagonalizableMap I J f ≫ (eJ).hom = (eI).hom ≫ f := by
  apply hom_ext_points
  intro T x
  apply (pointsEquiv J T).injective
  change pointsEquiv J T ((x ≫ (diagonalizableMap I J f).hom.hom) ≫ (eJ).hom.hom.hom) =
    pointsEquiv J T ((x ≫ (eI).hom.hom.hom) ≫ f.hom.hom)
  rw [diagonalizable_splitIso_points]
  change Diagonalizable.charEquiv (AddEquiv.refl (J → ℤ)) _
    (Corepresented.pointsEquiv _ _ T (x ≫ (diagonalizableMap I J f).hom.hom)) = _
  rw [diagonalizableMap, Corepresented.groupSchemeMap_points]
  funext j
  let χ : Multiplicative (I → ℤ) →* (Γ(T.left, ⊤))ˣ :=
    Corepresented.pointsEquiv (Diagonalizable.functor R (I → ℤ))
    (Diagonalizable.grpCorepresentation R (I → ℤ)) T x
  change χ (Multiplicative.ofAdd (characterMap I J f (Pi.single j 1))) = _
  change _ = Gm.pointsEquiv S T
    ((x ≫ (eI).hom.hom.hom) ≫ f.hom.hom ≫ (CommGroupScheme.groupHom (proj S J j)).hom.hom)
  change _ = Gm.pointsEquiv S T
    ((x ≫ (eI).hom.hom.hom) ≫ (CommGroupScheme.groupHom
      ((Additive.ofMul f : commGroupScheme S I ⟶ commGroupScheme S J) ≫ proj S J j)).hom.hom)
  rw [← (characterLatticeEquiv k I).symm_apply_apply
    ((Additive.ofMul f : commGroupScheme S I ⟶ commGroupScheme S J) ≫ proj S J j)]
  rw [pointsEquiv_characterLatticeEquiv_symm, diagonalizable_splitIso_points]
  rw [← characterMap_equiv, characterLatticeEquiv_proj]
  exact congrArg
    (fun ψ : Multiplicative (I → ℤ) →* (Γ(T.left, ⊤))ˣ =>
      ψ (Multiplicative.ofAdd (characterMap I J f (Pi.single j 1))))
    ((Diagonalizable.charEquiv (AddEquiv.refl (I → ℤ)) _).symm_apply_apply χ).symm

omit [DecidableEq I] [DecidableEq J] in
theorem diagonalizableMap_hom_left (f : splitTorus S I ⟶ splitTorus S J) :
    (diagonalizableMap I J f).hom.hom.left =
      Spec.map (CommRingCat.ofHom
        (Diagonalizable.incl R (characterMap I J f).toAddMonoidHom).hom.toRingHom) := by
  rw [diagonalizableMap, Corepresented.groupSchemeMap_hom_left]
  simp only [Corepresented.classify]
  erw [Diagonalizable.homEquiv_symm_restrict]
  erw [Equiv.symm_apply_apply, Category.comp_id]

/-- A finite split-torus morphism has finite cokernel on integral characters. -/
theorem characterMap_finite_cokernel (f : splitTorus S I ⟶ splitTorus S J)
    [IsFinite f.hom.hom.left] :
    Finite ((I → ℤ) ⧸ LinearMap.range (characterMap I J f)) := by
  have he : diagonalizableMap I J f = (eI).hom ≫ f ≫ (eJ).inv := by
    have h := congrArg (fun h => h ≫ (eJ).inv) (diagonalizableMap_splitIso I J f)
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h
  have hfin : IsFinite (diagonalizableMap I J f).hom.hom.left := by
    rw [he]
    change IsFinite ((eI).hom.hom.hom.left ≫ f.hom.hom.left ≫ (eJ).inv.hom.hom.left)
    infer_instance
  rw [diagonalizableMap_hom_left, IsFinite.SpecMap_iff] at hfin
  exact Diagonalizable.finite_cokernel_of_incl_finite
    (characterMap I J f).toAddMonoidHom hfin

omit [DecidableEq I] [DecidableEq J] in
/-- An epimorphism on schemes is injective on integral characters. -/
theorem characterMap_injective_of_epi (f : splitTorus S I ⟶ splitTorus S J)
    [Epi f.hom.hom.left] : Function.Injective (characterMap I J f) := by
  have : Epi f.hom.hom := Over.epi_of_epi_left _
  intro x y hxy
  have hc :
      (Additive.ofMul f : commGroupScheme S I ⟶ commGroupScheme S J) ≫
        (characterLatticeEquiv k J).symm x =
      (Additive.ofMul f : commGroupScheme S I ⟶ commGroupScheme S J) ≫
        (characterLatticeEquiv k J).symm y :=
    (characterLatticeEquiv k I).injective hxy
  apply (characterLatticeEquiv k J).symm.injective
  apply Additive.toMul.injective
  apply Grp.hom_ext
  apply (cancel_epi f.hom.hom).mp
  exact congrArg (fun z : characterLattice (commGroupScheme S I) =>
    (CommGroupScheme.groupHom z).hom.hom) hc

end splitTorus

end Langlands.GroupScheme
