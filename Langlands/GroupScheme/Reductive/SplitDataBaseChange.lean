import Langlands.GroupScheme.Reductive.SplitDataTransport

/-! # Actual coordinate split data under arbitrary scalar extension -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace splitTorus

/-- Successive coordinate pullback equals the direct coordinate pullback
followed by an actual ambient comparison, for any equal composite base map. -/
theorem exists_baseChangeHom_compIso {S S' S'' : Scheme.{u}}
    (a : S' ⟶ S) (b : S'' ⟶ S') (c : S'' ⟶ S) (hc : b ≫ a = c)
    (G : GroupScheme S) (I : Type u) [Fintype I] (i : splitTorus S I ⟶ G) :
    ∃ e : (baseChange c).obj G ≅ (baseChange b).obj ((baseChange a).obj G),
      (baseChangeIso b I).inv ≫
          (baseChange b).map ((baseChangeIso a I).inv ≫ (baseChange a).map i) =
        (baseChangeIso c I).inv ≫ (baseChange c).map i ≫ e.hom := by
  subst c
  refine ⟨baseChangeCompIso a b G, ?_⟩
  apply (cancel_mono (baseChangeCompIso a b G).inv).mp
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    baseChangeHom_comp a b I G i

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/-- Direct and successive scalar maps agree as actual scheme morphisms. -/
theorem algebraBaseMap_scalarTower :
    algebraBaseMap A B ≫ algebraBaseMap R A = algebraBaseMap R B := by
  simp only [algebraBaseMap, ← Spec.map_comp]
  congr 1
  ext r
  exact (IsScalarTower.algebraMap_apply R A B r).symm

variable (G : GroupScheme (Spec (CommRingCat.of R)))
  (I : Type u) [Fintype I]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)

/-- An actual ambient isomorphism compares successive and direct coordinate
inclusions for a scalar tower of arbitrary commutative rings. -/
theorem exists_baseChangeHom_scalarTowerIso :
    ∃ e : (baseChange (algebraBaseMap R B)).obj G ≅
        (baseChange (algebraBaseMap A B)).obj ((baseChange (algebraBaseMap R A)).obj G),
      baseChangeHom (K := B) ((baseChange (algebraBaseMap R A)).obj G) I
          (baseChangeHom (K := A) G I i) =
        baseChangeHom (K := B) G I i ≫ e.hom :=
  exists_baseChangeHom_compIso (algebraBaseMap R A) (algebraBaseMap A B)
    (algebraBaseMap R B) (algebraBaseMap_scalarTower (R := R) (A := A) (B := B)) G I i

/-- A scalar-tower comparison chosen together with its coordinate compatibility. -/
def baseChangeHomScalarTowerIso :
    (GroupScheme.baseChange (algebraBaseMap R B)).obj G ≅
      (GroupScheme.baseChange (algebraBaseMap A B)).obj
        ((GroupScheme.baseChange (algebraBaseMap R A)).obj G) :=
  (exists_baseChangeHom_scalarTowerIso (A := A) (B := B) G I i).choose

/-- The chosen scalar-tower comparison respects the actual coordinate inclusion. -/
theorem baseChangeHomScalarTowerIso_spec :
    baseChangeHom (K := B) ((GroupScheme.baseChange (algebraBaseMap R A)).obj G) I
        (baseChangeHom (K := A) G I i) =
      baseChangeHom (K := B) G I i ≫
        (baseChangeHomScalarTowerIso (A := A) (B := B) G I i).hom :=
  (exists_baseChangeHom_scalarTowerIso (A := A) (B := B) G I i).choose_spec

end splitTorus

section Field

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom]
  (I : Type u) [Fintype I]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)

local instance affineScalarPullback :
    IsAffineHom ((baseChange (algebraBaseMap R A)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R A)))

local instance affineFieldPullback {k : Type u} [Field k] [Algebra R k] :
    IsAffineHom ((baseChange (algebraBaseMap R k)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R k)))

local instance affineIteratedFieldPullback {k : Type u} [Field k] [Algebra A k] :
    IsAffineHom ((baseChange (algebraBaseMap A k)).obj
      ((baseChange (algebraBaseMap R A)).obj G)).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd
    ((baseChange (algebraBaseMap R A)).obj G).X.hom (algebraBaseMap A k)))

/-- The same actual full coordinate datum transfers from a direct field
fibre to the corresponding successive scalar pullback. -/
theorem IsRootDatumOf.baseChangeHom_scalarTower {J : Type v}
    {P : RootDatum J (I → ℤ) (I → ℤ)}
    (k : Type u) [Field k] [Algebra R k] [Algebra A k] [IsScalarTower R A k]
    (hP : IsRootDatumOf (splitTorus.baseChangeHom (K := k) G I i)
      (CoordinateRootDatum.fieldRealization k P)) :
    IsRootDatumOf
      (splitTorus.baseChangeHom (K := k) ((GroupScheme.baseChange (algebraBaseMap R A)).obj G) I
        (splitTorus.baseChangeHom (K := A) G I i))
      (CoordinateRootDatum.fieldRealization k P) := by
  obtain ⟨e, he⟩ := splitTorus.exists_baseChangeHom_scalarTowerIso (A := A) (B := k) G I i
  rw [he]
  exact hP.comp_iso e

/-- Arbitrary scalar extension preserves a supplied full coordinate datum
on every original field algebra, via its composite coefficient map. -/
theorem IsFibrewiseRootDatumOf.baseChange {J : Type v}
    {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hP : IsFibrewiseRootDatumOf I G i P) :
    IsFibrewiseRootDatumOf I ((GroupScheme.baseChange (algebraBaseMap R A)).obj G)
      (splitTorus.baseChangeHom (K := A) G I i) P := by
  refine ⟨hP.1, hP.2.1, fun k _ _ => ?_⟩
  let : Algebra R k := ((algebraMap A k).comp (algebraMap R A)).toAlgebra
  let : IsScalarTower R A k := IsScalarTower.of_algebraMap_eq' rfl
  exact IsRootDatumOf.baseChangeHom_scalarTower G I i k (hP.field k)

end Field

/-- A coordinate split torus maximal on every residue fibre stays so after
arbitrary pullback of the base, using the canonical coordinate comparison. -/
theorem IsFibrewiseMaximalTorus.baseChange_coordinates
    {S S' : Scheme.{u}} {G : GroupScheme S} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {I : Type u} [Fintype I] {i : splitTorus S I ⟶ G}
    (hi : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I) i)
    (a : S' ⟶ S) :
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S' I)
      ((splitTorus.baseChangeIso a I).inv ≫ (baseChange a).map i) := by
  intro s
  let b := S'.fromSpecResidueField s
  exact splitTorus.isMaximalTorus_baseChangedHom_comp I G i a b (hi.fieldPoint (b ≫ a))

end Langlands.GroupScheme
