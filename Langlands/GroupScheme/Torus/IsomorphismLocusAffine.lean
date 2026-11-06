import Langlands.GroupScheme.Torus.ClosedImmersionLocusAffine
import Langlands.GroupScheme.HopfMorphismBaseChange
import Langlands.GroupScheme.Torus.DiagonalizableHopf
import Langlands.CommutativeAlgebra.DiagonalIsomorphismLocus
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Isomorphism neighbourhoods for split tori over affine bases -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.TorusIsomorphismLocus

/-- A group-scheme homomorphism is invertible exactly when its underlying
scheme morphism is invertible. -/
theorem isIso_iff_underlying {S : Scheme.{u}} {H G : GroupScheme S} (f : H ⟶ G) :
    IsIso f ↔ IsIso f.hom.hom.left := by
  constructor
  · intro hf
    let := hf
    exact (Grp.forget _ ⋙ Over.forget _).map_isIso f
  · intro hf
    let : IsIso ((Over.forget S).map f.hom.hom) := hf
    let : IsIso f.hom.hom := isIso_of_reflects_iso f.hom.hom (Over.forget S)
    let e : H ≅ G := Grp.mkIso' (asIso f.hom.hom)
    change IsIso e.hom
    infer_instance

end Langlands.GroupScheme.TorusIsomorphismLocus

namespace Langlands.GroupScheme.HopfMorphismBaseChange

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

set_option backward.isDefEq.respectTransparency false in
/-- The actual base change of an affine spectrum morphism is invertible exactly
when its tensor coordinate map is bijective. -/
theorem isIso_baseChange_iff {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    IsIso
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map
        ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom f).op)).left) ↔
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id S S) f) := by
  rw [tensorSpecIso_naturality, isIso_comp_left_iff, isIso_comp_right_iff]
  exact isIso_SpecMap_iff

/-- Bijectivity in diagonal tensor coordinates is the actual affine
base-change isomorphism condition. -/
theorem isIso_diagonal_baseChange_iff {M : Type u} [AddCommMonoid M]
    {A : Type u} [CommRing A] [Algebra R A]
    (f : A →ₐ[R] AddMonoidAlgebra R M) :
    IsIso
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map
        ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom f).op)).left) ↔
      Function.Bijective
        (CommutativeAlgebra.DiagonalCoalgebraLocus.scalarExtension f S) := by
  rw [isIso_baseChange_iff, scalarExtension_eq]
  exact (Equiv.comp_bijective _
    (AddMonoidAlgebra.scalarTensorEquiv R S (M := M)).toEquiv).symm

/-- The criterion applies to actual base changes in the group-scheme category. -/
theorem isIso_hopf_diagonal_baseChange_iff {M : Type u} [AddCommGroup M]
    {A : Type u} [CommRing A] [HopfAlgebra R A]
    (f : A →ₐc[R] AddMonoidAlgebra R M) :
    IsIso
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map
        ((hopfSpec (CommRingCat.of R)).map (CommHopfAlgCat.ofHom f).op)) ↔
      Function.Bijective
        (CommutativeAlgebra.DiagonalCoalgebraLocus.scalarExtension f.toAlgHom S) := by
  rw [TorusIsomorphismLocus.isIso_iff_underlying]
  exact isIso_diagonal_baseChange_iff f.toAlgHom

/-- The two canonical coordinate systems have the same bijectivity condition. -/
theorem scalarExtension_bijective_iff {M N : Type u}
    [AddCommMonoid M] [AddCommMonoid N]
    (f : AddMonoidAlgebra R N →ₐc[R] AddMonoidAlgebra R M) :
    Function.Bijective (CommutativeAlgebra.DiagonalIsomorphismLocus.scalarExtension f S) ↔
      Function.Bijective
        (CommutativeAlgebra.DiagonalCoalgebraLocus.scalarExtension f.toAlgHom S) :=
  Equiv.bijective_comp
    (AddMonoidAlgebra.scalarTensorEquiv R S (M := N)).symm.toEquiv _

/-- For two diagonal groups, the actual base change is invertible exactly when
the canonical bialgebra scalar extension is bijective. -/
theorem isIso_hopf_split_baseChange_iff {M N : Type u}
    [AddCommGroup M] [AddCommGroup N]
    (f : AddMonoidAlgebra R N →ₐc[R] AddMonoidAlgebra R M) :
    IsIso
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map
        ((hopfSpec (CommRingCat.of R)).map (CommHopfAlgCat.ofHom f).op)) ↔
      Function.Bijective (CommutativeAlgebra.DiagonalIsomorphismLocus.scalarExtension f S) :=
  (isIso_hopf_diagonal_baseChange_iff f).trans (scalarExtension_bijective_iff f).symm

end Langlands.GroupScheme.HopfMorphismBaseChange

namespace Langlands.GroupScheme.TorusIsomorphismLocus

variable {R : CommRingCat.{u}} {M N : Type u} [AddCommGroup M] [AddCommGroup N]

/-- The standard diagonal group spectrum. -/
abbrev diagonalSource (R : CommRingCat.{u}) (M : Type u) [AddCommGroup M] :
    GroupScheme (Spec R) :=
  TorusClosedImmersionLocus.diagonalSource R M

/-- The actual contravariant bialgebra map of a diagonal group homomorphism. -/
def diagonalCoordinateMap (i : diagonalSource R M ⟶ diagonalSource R N) :
    AddMonoidAlgebra R N →ₐc[R] AddMonoidAlgebra R M :=
  (hopfSpec.fullyFaithful.preimage i).unop.hom

/-- Taking the Hopf spectrum recovers the given diagonal homomorphism. -/
theorem diagonalCoordinateMap_map (i : diagonalSource R M ⟶ diagonalSource R N) :
    (hopfSpec R).map (CommHopfAlgCat.ofHom (diagonalCoordinateMap i)).op = i :=
  hopfSpec.fullyFaithful.map_preimage _

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Base change of the supplied diagonal homomorphism is an isomorphism exactly
when its canonical coordinate scalar extension is bijective. -/
theorem diagonal_iso_iff (i : diagonalSource R M ⟶ diagonalSource R N)
    (A : Type u) [CommRing A] [Algebra R A] :
    IsIso ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map i) ↔
      Function.Bijective
        (CommutativeAlgebra.DiagonalIsomorphismLocus.scalarExtension
          (R := R) (M := M) (N := N)
          (diagonalCoordinateMap (R := R) (M := M) (N := N) i) A) := by
  simpa only [diagonalCoordinateMap_map] using
    (HopfMorphismBaseChange.isIso_hopf_split_baseChange_iff
      (R := R) (S := A) (M := M) (N := N) (diagonalCoordinateMap i))

set_option backward.isDefEq.respectTransparency false in
/-- A field-specialized isomorphism between finite-source diagonal algebras
extends to an actual group-scheme isomorphism over a principal neighbourhood. -/
theorem exists_open_hopf_diagonal [AddMonoid.FG N]
    (f : AddMonoidAlgebra R N →ₐc[R] AddMonoidAlgebra R M)
    (K : Type u) [Field K] [Algebra R K]
    (hx : IsIso
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
        ((hopfSpec R).map (CommHopfAlgCat.ofHom f).op))) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Spec R), IsOpenImmersion q ∧
      ∃ bx : Spec (CommRingCat.of K) ⟶ V,
        bx ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R K)) ∧
          IsIso ((baseChange q).map ((hopfSpec R).map (CommHopfAlgCat.ofHom f).op)) := by
  have hφ := (HopfMorphismBaseChange.isIso_hopf_split_baseChange_iff f).mp hx
  obtain ⟨r, hr, hiso⟩ :=
    CommutativeAlgebra.DiagonalIsomorphismLocus.exists_principal_isomorphism_certificate f K hφ
  let V := Spec (CommRingCat.of (Localization.Away r))
  let q : V ⟶ Spec R :=
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
  let kmap : Localization.Away r →+* K :=
    IsLocalization.Away.lift r (g := algebraMap R K) (isUnit_iff_ne_zero.mpr hr)
  let bx : Spec (CommRingCat.of K) ⟶ V := Spec.map (CommRingCat.ofHom kmap)
  refine ⟨V, q, inferInstance, bx, ?_, ?_⟩
  · change Spec.map (CommRingCat.ofHom kmap) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) = _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact IsLocalization.Away.lift_comp r (g := algebraMap R K)
      (isUnit_iff_ne_zero.mpr hr)
  · exact (HopfMorphismBaseChange.isIso_hopf_split_baseChange_iff f).mpr
      (hiso (Localization.Away r) (IsLocalization.Away.algebraMap_isUnit _))

/-- The neighbourhood construction applies to a supplied actual diagonal
group homomorphism. -/
theorem exists_open_diagonal [AddMonoid.FG N]
    (i : diagonalSource R M ⟶ diagonalSource R N)
    (K : Type u) [Field K] [Algebra R K]
    (hx : IsIso ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map i)) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Spec R), IsOpenImmersion q ∧
      ∃ bx : Spec (CommRingCat.of K) ⟶ V,
        bx ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R K)) ∧
          IsIso ((baseChange q).map i) := by
  have h := exists_open_hopf_diagonal (diagonalCoordinateMap i) K
  simp only [diagonalCoordinateMap_map] at h
  exact h hx

/-- Isomorphic source and target presentations preserve the base-change
isomorphism condition. -/
theorem iso_baseChange_prepost_iff {S S' : Scheme.{u}} (b : S' ⟶ S)
    {H H' G G' : GroupScheme S} (eH : H' ≅ H) (eG : G' ≅ G) (i : H ⟶ G) :
    IsIso ((baseChange b).map (eH.hom ≫ i ≫ eG.inv)) ↔
      IsIso ((baseChange b).map i) := by
  simp only [Functor.map_comp, isIso_comp_left_iff, isIso_comp_right_iff]

/-- Over an affine base, a field-valued isomorphism between split tori extends
to an actual isomorphism over an open neighbourhood of that field point. -/
theorem exists_open_affine_algebraMap {H G : GroupScheme (Spec R)}
    (hH : IsSplitTorus H) (hG : IsSplitTorus G) (i : H ⟶ G)
    (K : Type u) [Field K] [Algebra R K]
    (hx : IsIso ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map i)) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Spec R), IsOpenImmersion q ∧
      ∃ bx : Spec (CommRingCat.of K) ⟶ V,
        bx ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R K)) ∧
          IsIso ((baseChange q).map i) := by
  classical
  obtain ⟨I, hI, ⟨eH⟩⟩ := hH
  obtain ⟨J, hJ, ⟨eG⟩⟩ := hG
  let := Fintype.ofFinite I
  let := Fintype.ofFinite J
  let eH' : diagonalSource R (I → ℤ) ≅ H :=
    Diagonalizable.hopfSpecIso R (I → ℤ) ≪≫
      Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ)) ≪≫ eH.symm
  let eG' : diagonalSource R (J → ℤ) ≅ G :=
    Diagonalizable.hopfSpecIso R (J → ℤ) ≪≫
      Diagonalizable.splitIso R (AddEquiv.refl (J → ℤ)) ≪≫ eG.symm
  have hj := (iso_baseChange_prepost_iff _ eH' eG' i).mpr hx
  obtain ⟨V, q, hq, bx, hbx, hjq⟩ :=
    exists_open_diagonal (eH'.hom ≫ i ≫ eG'.inv) K hj
  exact ⟨V, q, hq, bx, hbx, (iso_baseChange_prepost_iff q eH' eG' i).mp hjq⟩

/-- The affine-base construction retains the exact factorization of an
arbitrary supplied field-valued point. -/
theorem exists_open_affine {H G : GroupScheme (Spec R)}
    (hH : IsSplitTorus H) (hG : IsSplitTorus G) (i : H ⟶ G)
    (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ Spec R)
    (hx : IsIso ((baseChange x).map i)) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Spec R), IsOpenImmersion q ∧
      ∃ bx : Spec (CommRingCat.of K) ⟶ V, bx ≫ q = x ∧
        IsIso ((baseChange q).map i) := by
  obtain ⟨f, rfl⟩ := Spec.homEquiv.symm.surjective x
  let : Algebra R K := f.hom.toAlgebra
  exact exists_open_affine_algebraMap hH hG i K hx

end Langlands.GroupScheme.TorusIsomorphismLocus
