import Langlands.GroupScheme.Reductive.LocalRootGroupFibre
import Langlands.GroupScheme.Dynamic.RingPointCoordinates
import Langlands.GroupScheme.Reductive.LocalSplitBigCellProof
import Langlands.GroupScheme.Rational.RootSubgroupPositive
import Langlands.GroupScheme.Rational.CocharacterCentralizer
import Langlands.GroupScheme.Rational.RootFactorPairReflection
import Langlands.GroupScheme.Reductive.RootReducednessReduction
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.AlgebraicGeometry.SmoothReducedBase
import Langlands.GroupScheme.SmoothProducts
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Root parametrizations over a reduced local ring -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Polynomial

namespace Langlands.GroupScheme.LocalRootGroup

open Corepresented LocalSplitCell

/-! ### Checking equalities at field points -/

/-- Two morphisms out of a reduced scheme into a separated one agree if they agree at every
field-valued point. -/
theorem ext_of_fieldPoints {S : Scheme.{u}} {X Y : Over S} [IsReduced X.left] [IsSeparated Y.hom]
    (f g : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (t : Over.mk s ⟶ X),
      t ≫ f = t ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  refine ext_of_fromSpecResidueField_eq f.left g.left Y.hom Set.univ dense_univ ?_
    (by rw [Over.w f, Over.w g])
  intro w _
  exact congrArg Over.Hom.left (h (X.left.residueField w)
    (X.left.fromSpecResidueField w ≫ X.hom) (Over.homMk (X.left.fromSpecResidueField w) rfl))

/-- A field-valued point of `Spec R` makes the field an `R`-algebra with that structure map. -/
theorem exists_algebra_of_fieldPoint {R : Type u} [CommRing R] {K : Type u} [Field K]
    (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) :
    ∃ _ : Algebra R K, algebraBaseMap R K = s := by
  refine ⟨(Spec.preimage s).hom.toAlgebra, ?_⟩
  change Spec.map (CommRingCat.ofHom (Spec.preimage s).hom) = s
  rw [CommRingCat.ofHom_hom]
  exact Spec.map_preimage s

/-! ### Scalar points of `𝔾ₐ` -/

section Scalar

variable {A : CommRingCat.{u}}

theorem scalarPoint_add (T : Over (Spec A)) (c c' : Γ(T.left, ⊤)) :
    VectorGroup.scalarPoint A T (c + c') =
      VectorGroup.scalarPoint A T c * VectorGroup.scalarPoint A T c' := by
  apply VectorGroup.points_ext
  intro j
  have h := congrFun (VectorGroup.coordinates_mul (VectorGroup.scalarPoint A T c)
    (VectorGroup.scalarPoint A T c')) j
  rw [Pi.add_apply, VectorGroup.coordinates_scalarPoint, VectorGroup.coordinates_scalarPoint] at h
  rw [VectorGroup.coordinates_scalarPoint, h]

theorem scalarPoint_zero (T : Over (Spec A)) : VectorGroup.scalarPoint A T 0 = 1 := by
  apply VectorGroup.points_ext
  intro j
  rw [VectorGroup.coordinates_scalarPoint, map_one]
  rfl

variable (A) in
theorem scalarPoint_bijective (T : Over (Spec A)) :
    Function.Bijective (VectorGroup.scalarPoint A T) := by
  refine ⟨fun c c' h => ?_, fun v => ⟨(VectorGroup.coordinates A 1 T v).toAdd 0, ?_⟩⟩
  · have := congrArg (fun v => (VectorGroup.coordinates A 1 T v).toAdd 0) h
    simpa only [VectorGroup.coordinates_scalarPoint] using this
  · apply VectorGroup.points_ext
    intro j
    rw [VectorGroup.coordinates_scalarPoint]
    exact congrArg (fun k => (VectorGroup.coordinates A 1 T v).toAdd k) (Subsingleton.elim 0 j)

end Scalar

variable {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] {I : Type u} [Fintype I]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (mu nu : I → ℤ)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-! ### The coordinate of points of the root group -/

section Coord

variable (x : coordU i mu nu)

/-- The value of the coordinate `x` at a point of `U`. -/
def coordX {T : Over (Spec (CommRingCat.of R))} (y : T ⟶ (Uc i mu nu).X) : Γ(T.left, ⊤) :=
  y.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of (coordU i mu nu))).inv x)

theorem coordX_comp {T T' : Over (Spec (CommRingCat.of R))} (a : T' ⟶ T)
    (y : T ⟶ (Uc i mu nu).X) : coordX i mu nu x (a ≫ y) = a.left.appTop (coordX i mu nu x y) := by
  rw [coordX, coordX, Over.comp_left, Scheme.Hom.comp_appTop]
  rfl

theorem eval_bijective
    (hx : Function.Bijective (Polynomial.aeval x : R[X] →ₐ[R] coordU i mu nu))
    (A : CommAlgCat.{u} (CommRingCat.of R)) :
    Function.Bijective fun φ : coordU i mu nu ⟶ A => φ.hom x := by
  let e := AlgEquiv.ofBijective (Polynomial.aeval x : R[X] →ₐ[R] coordU i mu nu) hx
  have hex : e Polynomial.X = x := Polynomial.aeval_X x
  constructor
  · intro φ φ' h
    apply CommAlgCat.hom_ext
    have h2 : φ.hom.comp e.toAlgHom = φ'.hom.comp e.toAlgHom := by
      apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hex]
      exact h
    ext b
    obtain ⟨p, rfl⟩ := e.surjective b
    exact congrArg (fun ψ : R[X] →ₐ[R] A => ψ p) h2
  · intro a
    refine ⟨CommAlgCat.ofHom ((Polynomial.aeval a).comp e.symm.toAlgHom), ?_⟩
    change (Polynomial.aeval a) (e.symm x) = a
    rw [← hex, AlgEquiv.symm_apply_apply, Polynomial.aeval_X]

theorem coordX_bijective
    (hx : Function.Bijective (Polynomial.aeval x : R[X] →ₐ[R] coordU i mu nu))
    (T : Over (Spec (CommRingCat.of R))) : Function.Bijective (coordX i mu nu x (T := T)) := by
  have h1 : coordX i mu nu x (T := T) = (fun φ => φ.hom x) ∘
      fun y => (cutCorepresentableBy _).homEquiv.symm (Corepresented.pointsEquiv _ _ T y) := by
    funext y
    exact (homEquiv_symm_pointsEquiv_apply T y x).symm
  rw [h1]
  exact (eval_bijective i mu nu x hx _).comp (((Corepresented.pointsEquiv _ _ T).toEquiv.trans
    (cutCorepresentableBy _).homEquiv.symm).bijective)

end Coord

/-! ### Field points -/

section FieldLevel

variable {i mu nu} {K : Type u} [Field K] [Algebra R K] (Φ : Ga K ≅ UK i mu nu K)
  {D : Type u} [CommRing D] [Algebra R D] [Algebra K D] [IsScalarTower R K D]

/-- The underlying point over `R` of a point of `U_K`. -/
def under (z : RingCoordinates.testOver K D ⟶ (UK i mu nu K).X) :
    RingCoordinates.specOver (CommRingCat.of R) D ⟶ (Uc i mu nu).X :=
  RingCoordinates.testOverHom (CommRingCat.of R) K D ≫
    GroupScheme.baseChangePointsEquiv (RingCoordinates.baseMap (CommRingCat.of R) K) (Uc i mu nu) _ z

theorem under_mul (z z' : RingCoordinates.testOver K D ⟶ (UK i mu nu K).X) :
    under (z * z') = under z * under z' := by
  rw [under, under, under, map_mul, MonObj.comp_mul]

theorem under_bijective :
    Function.Bijective (under (i := i) (mu := mu) (nu := nu) (K := K) (D := D)) := by
  refine Function.Bijective.comp ?_ (GroupScheme.baseChangePointsEquiv _ _ _).bijective
  refine ⟨fun y y' h => ?_, fun y => ⟨RingCoordinates.testOverInv (CommRingCat.of R) K D ≫ y, ?_⟩⟩
  · have := congrArg (fun z => RingCoordinates.testOverInv (CommRingCat.of R) K D ≫ z) h
    simpa only [← Category.assoc, RingCoordinates.testOverInv_comp_testOverHom, Category.id_comp] using this
  · simp only [← Category.assoc, RingCoordinates.testOverHom_comp_testOverInv, Category.id_comp]

omit [Algebra R D] [IsScalarTower R K D] in
theorem fibrePoint_add (d d' : D) :
    fibrePoint i mu nu Φ D (d + d') = fibrePoint i mu nu Φ D d * fibrePoint i mu nu Φ D d' := by
  rw [fibrePoint, fibrePoint, fibrePoint, map_add, scalarPoint_add, MonObj.mul_comp]

variable (x : coordU i mu nu)

theorem coordX_under_fibrePoint (d : D) :
    coordX i mu nu x (under (fibrePoint i mu nu Φ D d)) =
      (Scheme.ΓSpecIso (CommRingCat.of D)).inv
        (Polynomial.aeval d (fibreAlgHom i mu nu Φ K[X] Polynomial.X x)) := by
  rw [coordX, Corepresented.appTop_ΓSpecIso_inv]
  congr 1
  have h := fibreAlgHom_comp i mu nu Φ (Polynomial.aeval d) Polynomial.X
  rw [Polynomial.aeval_X] at h
  exact congrArg (fun φ : coordU i mu nu →ₐ[CommRingCat.of R] D => φ x) h

/-- On field points, the coordinate is additive. -/
theorem coordX_mul_field {u : K}
    (hψ : fibreAlgHom i mu nu Φ K[X] Polynomial.X x = Polynomial.C u * Polynomial.X)
    (y y' : RingCoordinates.specOver (CommRingCat.of R) K ⟶ (Uc i mu nu).X) :
    coordX i mu nu x (y * y') = coordX i mu nu x y + coordX i mu nu x y' := by
  obtain ⟨z, rfl⟩ := (under_bijective (i := i) (mu := mu) (nu := nu) (K := K) (D := K)).2 y
  obtain ⟨z', rfl⟩ := (under_bijective (i := i) (mu := mu) (nu := nu) (K := K) (D := K)).2 y'
  obtain ⟨d, rfl⟩ := (fibrePoint_bijective i mu nu Φ K).2 z
  obtain ⟨d', rfl⟩ := (fibrePoint_bijective i mu nu Φ K).2 z'
  rw [← under_mul, ← fibrePoint_add, coordX_under_fibrePoint, coordX_under_fibrePoint,
    coordX_under_fibrePoint, hψ, ← map_add]
  congr 1
  simp only [map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Algebra.algebraMap_self,
    RingHom.id_apply]
  ring

end FieldLevel

/-! ### Smoothness -/

section Smooth

variable [Smooth G.X.hom]

theorem smooth_coordG : Algebra.Smooth (CommRingCat.of R) (AffineCoordinates.algebra G) :=
  (DynamicSmooth.smooth_algSpec_iff (AffineCoordinates.algebra G)).1
    (smooth_of_over_iso ((Grp.forget _).mapIso (AffineCoordinates.groupSchemeIso G))
      (inferInstance : Smooth G.X.hom))

theorem smooth_coordZ :
    Algebra.Smooth (CommRingCat.of R) (quotientAlgebra (centralizerIdeal (centCochar i mu))) := by
  have := smooth_coordG (G := G)
  exact (DynamicSmooth.smooth_algSpec_iff _).1
    (DynamicSmoothRing.smooth_centralizerScheme (centCochar i mu))

theorem smooth_Uc : Smooth (Uc i mu nu).X.hom := by
  have := smooth_coordZ i mu
  exact DynamicSmoothRing.smooth_unipotentScheme (unipCochar i mu nu)

end Smooth

/-! ### The coordinate is additive -/

section Additive

variable [Smooth G.X.hom] [IsReduced R] (x : coordU i mu nu)
  (hψ : ∀ (K : Type u) [Field K] [Algebra R K], ∃ (Φ : Ga K ≅ UK i mu nu K) (u : K),
    fibreAlgHom i mu nu Φ K[X] Polynomial.X x = Polynomial.C u * Polynomial.X)

include hψ in
theorem coordX_mul {T : Over (Spec (CommRingCat.of R))} (y y' : T ⟶ (Uc i mu nu).X) :
    coordX i mu nu x (y * y') = coordX i mu nu x y + coordX i mu nu x y' := by
  have := smooth_Uc i mu nu
  have : Smooth ((Uc i mu nu).X ⊗ (Uc i mu nu).X).hom := smooth_tensor _ _ inferInstance inferInstance
  have : IsReduced ((Uc i mu nu).X ⊗ (Uc i mu nu).X).left :=
    Langlands.AlgebraicGeometry.SmoothReducedBase.isReduced_of_smooth_of_isReduced
      ((Uc i mu nu).X ⊗ (Uc i mu nu).X).hom
  have key : coordX i mu nu x (fst (Uc i mu nu).X (Uc i mu nu).X * snd _ _) =
      coordX i mu nu x (fst (Uc i mu nu).X (Uc i mu nu).X) +
        coordX i mu nu x (snd (Uc i mu nu).X (Uc i mu nu).X) := by
    have hfg : VectorGroup.scalarPoint (CommRingCat.of R) _
        (coordX i mu nu x (fst (Uc i mu nu).X (Uc i mu nu).X * snd _ _)) =
        VectorGroup.scalarPoint (CommRingCat.of R) _
          (coordX i mu nu x (fst (Uc i mu nu).X (Uc i mu nu).X) +
            coordX i mu nu x (snd (Uc i mu nu).X (Uc i mu nu).X)) := by
      have : IsSeparated (VectorGroup.groupScheme (CommRingCat.of R) 1).X.hom := by
        change IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin 1) R))))
        infer_instance
      apply ext_of_fieldPoints
      intro K _ s t
      obtain ⟨_, rfl⟩ := exists_algebra_of_fieldPoint s
      obtain ⟨Φ, u, hu⟩ := hψ K
      rw [VectorGroup.scalarPoint_comp, VectorGroup.scalarPoint_comp, map_add, ← coordX_comp,
        ← coordX_comp, ← coordX_comp, MonObj.comp_mul]
      congr 1
      exact coordX_mul_field Φ x hu (t ≫ fst _ _) (t ≫ snd _ _)
    have := congrArg (fun v => (VectorGroup.coordinates _ 1 _ v).toAdd 0) hfg
    simpa only [VectorGroup.coordinates_scalarPoint] using this
  have h := congrArg (fun c => (lift y y').left.appTop c) key
  simp only [map_add] at h
  rw [← coordX_comp, ← coordX_comp, ← coordX_comp, MonObj.comp_mul, lift_fst, lift_snd] at h
  exact h

end Additive

/-- The inclusion `U ⟶ Z ⟶ G`. -/
abbrev incl : Uc i mu nu ⟶ G := jU i mu nu ≫ jZ i mu ≫ (AffineCoordinates.groupSchemeIso G).hom

/-! ### The parametrization `𝔾ₐ ≅ U` -/

section Param

variable (x : coordU i mu nu)
  (hx : Function.Bijective (Polynomial.aeval x : R[X] →ₐ[R] coordU i mu nu))
  (hadd : ∀ (T : Over (Spec (CommRingCat.of R))) (y y' : T ⟶ (Uc i mu nu).X),
    coordX i mu nu x (y * y') = coordX i mu nu x y + coordX i mu nu x y')

include hadd in
theorem coordX_one (T : Over (Spec (CommRingCat.of R))) :
    coordX i mu nu x (1 : T ⟶ (Uc i mu nu).X) = 0 := by
  have h := hadd T 1 1
  rw [mul_one] at h
  linear_combination -h

/-- The coordinate as a homomorphism from the points of `U` to the points of `𝔾ₐ`. -/
def coordHom (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ (Uc i mu nu).X) →* (T ⟶ (Ga R).X) where
  toFun y := VectorGroup.scalarPoint _ T (coordX i mu nu x y)
  map_one' := by rw [coordX_one i mu nu x hadd, scalarPoint_zero]
  map_mul' y y' := by rw [hadd, scalarPoint_add]

include hx in
theorem coordHom_bijective (T : Over (Spec (CommRingCat.of R))) :
    Function.Bijective (coordHom i mu nu x hadd T) :=
  (scalarPoint_bijective _ T).comp (coordX_bijective i mu nu x hx T)

/-- The points of `U` are the points of `𝔾ₐ`, through the coordinate `x`. -/
def pointsEquivGa (T : Over (Spec (CommRingCat.of R))) : (T ⟶ (Uc i mu nu).X) ≃* (T ⟶ (Ga R).X) :=
  MulEquiv.ofBijective (coordHom i mu nu x hadd T) (coordHom_bijective i mu nu x hx hadd T)

theorem pointsEquivGa_apply (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ (Uc i mu nu).X) :
    pointsEquivGa i mu nu x hx hadd T y = VectorGroup.scalarPoint _ T (coordX i mu nu x y) :=
  rfl

theorem pointsEquivGa_naturality {T T' : Over (Spec (CommRingCat.of R))} (a : T' ⟶ T)
    (y : T ⟶ (Uc i mu nu).X) :
    pointsEquivGa i mu nu x hx hadd T' (a ≫ y) = a ≫ pointsEquivGa i mu nu x hx hadd T y := by
  rw [pointsEquivGa_apply, pointsEquivGa_apply, coordX_comp, VectorGroup.scalarPoint_comp]

/-- The isomorphism `𝔾ₐ ≅ U` given by the coordinate `x`. -/
def gaIsoU : Ga R ≅ Uc i mu nu :=
  (isoOfPoints (pointsEquivGa i mu nu x hx hadd) (pointsEquivGa_naturality i mu nu x hx hadd)).symm

theorem coordX_gaIsoU (T : Over (Spec (CommRingCat.of R))) (c : Γ(T.left, ⊤)) :
    coordX i mu nu x (VectorGroup.scalarPoint _ T c ≫ (gaIsoU i mu nu x hx hadd).hom.hom.hom) =
      c := by
  apply (scalarPoint_bijective _ T).1
  rw [gaIsoU, Iso.symm_hom, comp_isoOfPoints_inv]
  exact (pointsEquivGa i mu nu x hx hadd T).apply_symm_apply _

/-- The root map `𝔾ₐ ≅ U ⊆ Z ⊆ G`. -/
def rootMap : Ga R ⟶ G :=
  (gaIsoU i mu nu x hx hadd).hom ≫ incl i mu nu

theorem isClosedSubgroup_rootMap : IsClosedSubgroup (rootMap i mu nu x hx hadd) :=
  (IsClosedSubgroup.of_iso _).comp ((Corepresented.isClosedSubgroup_unipotentHom _).comp
    ((Corepresented.isClosedSubgroup_centralizerHom _).comp_iso _))

theorem rootPoint_rootMap (T : Over (Spec (CommRingCat.of R))) (c : Γ(T.left, ⊤)) :
    rootPoint (rootMap i mu nu x hx hadd) T c =
      (VectorGroup.scalarPoint _ T c ≫ (gaIsoU i mu nu x hx hadd).hom.hom.hom) ≫
        (incl i mu nu).hom.hom := by
  rw [rootPoint, rootMap, Grp.comp_hom_hom, Category.assoc]

end Param

/-! ### Torus equivariance on field points -/

section FieldEquivariance

variable {i mu nu} {K : Type u} [Field K] [Algebra R K] (Φ : Ga K ≅ UK i mu nu K)

theorem under_comp_incl (z : RingCoordinates.testOver K K ⟶ (UK i mu nu K).X) :
    under z ≫ (incl i mu nu).hom.hom =
      RingCoordinates.testOverHom (CommRingCat.of R) K K ≫
        GroupScheme.baseChangePointsEquiv (algebraBaseMap R K) G _
          (z ≫ ((GroupScheme.baseChange (algebraBaseMap R K)).map (incl i mu nu)).hom.hom) := by
  rw [under, Category.assoc, ← GroupScheme.baseChangePointsEquiv_comp]

omit [IsAffineHom G.X.hom] in
variable (R) in
/-- The torus point over `R` underlying a torus point of a field fibre. -/
def underT (t : RingCoordinates.testOver K K ⟶ (splitTorus (Spec (CommRingCat.of K)) I).X) :
    RingCoordinates.specOver (CommRingCat.of R) K ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X :=
  RingCoordinates.testOverHom (CommRingCat.of R) K K ≫
    GroupScheme.baseChangePointsEquiv (algebraBaseMap R K) (splitTorus _ I) _
      (t ≫ (splitTorus.baseChangeIso (algebraBaseMap R K) I).inv.hom.hom)

omit [IsAffineHom G.X.hom] in
theorem underT_comp (t : RingCoordinates.testOver K K ⟶ (splitTorus (Spec (CommRingCat.of K)) I).X) :
    underT R t ≫ i.hom.hom =
      RingCoordinates.testOverHom (CommRingCat.of R) K K ≫
        GroupScheme.baseChangePointsEquiv (algebraBaseMap R K) G _
          (t ≫ (splitTorus.baseChangeHom (K := K) G I i).hom.hom) := by
  rw [underT, Category.assoc, LocalSplitBigCell.baseChangePointsEquiv_torus]

omit [IsAffineHom G.X.hom] in
theorem underT_surjective :
    Function.Surjective (underT R (I := I) (K := K)) := by
  intro t'
  refine ⟨(GroupScheme.baseChangePointsEquiv (algebraBaseMap R K) (splitTorus _ I) _).symm
    (RingCoordinates.testOverInv (CommRingCat.of R) K K ≫ t') ≫
      (splitTorus.baseChangeIso (algebraBaseMap R K) I).hom.hom.hom, ?_⟩
  rw [underT, Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom,
    Category.comp_id, MulEquiv.apply_symm_apply, ← Category.assoc, RingCoordinates.testOverHom_comp_testOverInv,
    Category.id_comp]

/-- Conjugating a point of `U` over a field by a torus point scales its parameter. -/
theorem conj_under (α : characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I))
    (hΦ : ∀ (Z : Over (Spec (CommRingCat.of K)))
        (t : Z ⟶ (splitTorus (Spec (CommRingCat.of K)) I).X) (x : Z ⟶ (Ga K).X),
      (t ≫ (tK i mu K).hom.hom) *
          (x ≫ (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)).hom.hom) *
          (t ≫ (tK i mu K).hom.hom)⁻¹ =
        VectorGroup.weightPointAction α Z t x ≫
          (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)).hom.hom)
    (t : RingCoordinates.testOver K K ⟶ (splitTorus (Spec (CommRingCat.of K)) I).X) (d : K) :
    (underT R t ≫ i.hom.hom) * (under (fibrePoint i mu nu Φ K d) ≫ (incl i mu nu).hom.hom) *
        (underT R t ≫ i.hom.hom)⁻¹ =
      under (fibrePoint i mu nu Φ K ((Scheme.ΓSpecIso (CommRingCat.of K)).hom
          (VectorGroup.charValue α (RingCoordinates.testOver K K) t) * d)) ≫ (incl i mu nu).hom.hom := by
  rw [underT_comp, under_comp_incl, under_comp_incl, ← GrpObj.comp_inv, ← MonObj.comp_mul,
    ← MonObj.comp_mul, ← map_inv, ← map_mul, ← map_mul]
  refine congrArg (fun z => RingCoordinates.testOverHom (CommRingCat.of R) K K ≫
    GroupScheme.baseChangePointsEquiv (algebraBaseMap R K) G _ z) ?_
  have hmap : (GroupScheme.baseChange (algebraBaseMap R K)).map (incl i mu nu) =
      (GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu) ≫ jZK i mu K := by
    rw [incl, jZK, ← Functor.map_comp]
  have e1 : t ≫ (splitTorus.baseChangeHom (K := K) G I i).hom.hom =
      (t ≫ (tK i mu K).hom.hom) ≫ (jZK i mu K).hom.hom := by
    simp only [← tK_comp i mu K, Grp.comp_hom_hom, Category.assoc]
  have e2 : ∀ z : RingCoordinates.testOver K K ⟶ (UK i mu nu K).X,
      z ≫ ((GroupScheme.baseChange (algebraBaseMap R K)).map (incl i mu nu)).hom.hom =
        (z ≫ ((GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)).hom.hom) ≫
          (jZK i mu K).hom.hom := by
    intro z
    simp only [hmap, Grp.comp_hom_hom, Category.assoc]
  rw [e1, e2, e2, ← GrpObj.inv_comp, ← MonObj.mul_comp, ← MonObj.mul_comp]
  congr 1
  have h1 := hΦ (RingCoordinates.testOver K K) t (VectorGroup.scalarPoint (CommRingCat.of K) (RingCoordinates.testOver K K)
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv d))
  rw [weightPointAction_scalarPoint] at h1
  simp only [fibrePoint, Grp.comp_hom_hom, Category.assoc] at h1 ⊢
  rw [h1, map_mul, Iso.hom_inv_id_apply]

omit [IsAffineHom G.X.hom] in
theorem charValue_underT (a : I → ℤ)
    (t : RingCoordinates.testOver K K ⟶ (splitTorus (Spec (CommRingCat.of K)) I).X) :
    VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
        (splitTorus.exponentCharacter _ I a) _ (underT R t) =
      VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
        (splitTorus.exponentCharacter _ I a) (RingCoordinates.testOver K K) t := by
  rw [underT, VectorGroup.charValue_comp,
    LocalSplitBigCell.charValue_exponentCharacter_baseChange (R := R) K a t]
  rfl

end FieldEquivariance

/-! ### Torus equivariance of the root map -/

section RootEquivariance

variable (x : coordU i mu nu)
  (hx : Function.Bijective (Polynomial.aeval x : R[X] →ₐ[R] coordU i mu nu))
  (hadd : ∀ (T : Over (Spec (CommRingCat.of R))) (y y' : T ⟶ (Uc i mu nu).X),
    coordX i mu nu x (y * y') = coordX i mu nu x y + coordX i mu nu x y')

/-- The torus acts on the root map through `a`, on points over a field. -/
theorem rootMap_equivariant_field (a : I → ℤ) {K : Type u} [Field K] [Algebra R K]
    (Φ : Ga K ≅ UK i mu nu K)
    (hΦ : ∀ (Z : Over (Spec (CommRingCat.of K)))
        (t : Z ⟶ (splitTorus (Spec (CommRingCat.of K)) I).X) (x : Z ⟶ (Ga K).X),
      (t ≫ (tK i mu K).hom.hom) *
          (x ≫ (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)).hom.hom) *
          (t ≫ (tK i mu K).hom.hom)⁻¹ =
        VectorGroup.weightPointAction (splitTorus.exponentCharacter _ I a) Z t x ≫
          (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)).hom.hom)
    {u0 : K} (hψ : fibreAlgHom i mu nu Φ K[X] Polynomial.X x = Polynomial.C u0 * Polynomial.X)
    (t' : RingCoordinates.specOver (CommRingCat.of R) K ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X)
    (c : Γ((RingCoordinates.specOver (CommRingCat.of R) K).left, ⊤)) :
    (t' ≫ i.hom.hom) * rootPoint (rootMap i mu nu x hx hadd) _ c * (t' ≫ i.hom.hom)⁻¹ =
      rootPoint (rootMap i mu nu x hx hadd) _
        (VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
          (splitTorus.exponentCharacter _ I a) _ t' * c) := by
  have hu0 : u0 ≠ 0 := by
    rintro rfl
    have h0 : ∀ d : K, coordX i mu nu x (under (fibrePoint i mu nu Φ K d)) = 0 := by
      intro d
      rw [coordX_under_fibrePoint, hψ]
      simp
    have h01 := (coordX_bijective i mu nu x hx _).1 ((h0 0).trans (h0 1).symm)
    exact zero_ne_one ((fibrePoint_bijective i mu nu Φ K).1 (under_bijective.1 h01))
  have key : ∀ d : K, VectorGroup.scalarPoint _ _
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv (u0 * d)) ≫
        (gaIsoU i mu nu x hx hadd).hom.hom.hom = under (fibrePoint i mu nu Φ K d) := by
    intro d
    apply (coordX_bijective i mu nu x hx _).1
    rw [coordX_gaIsoU, coordX_under_fibrePoint, hψ]
    simp
  obtain ⟨t, rfl⟩ := underT_surjective t'
  obtain ⟨d, rfl⟩ : ∃ d : K, (Scheme.ΓSpecIso (CommRingCat.of K)).inv (u0 * d) = c :=
    ⟨u0⁻¹ * (Scheme.ΓSpecIso (CommRingCat.of K)).hom c, by
      rw [← mul_assoc, mul_inv_cancel₀ hu0, one_mul, Iso.hom_inv_id_apply]⟩
  have hc : ∀ c : Γ((RingCoordinates.specOver (CommRingCat.of R) K).left, ⊤),
      c = (Scheme.ΓSpecIso (CommRingCat.of K)).inv (u0 * d) →
      VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
        (splitTorus.exponentCharacter _ I a) _ (underT R t) * c =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv (u0 * ((Scheme.ΓSpecIso (CommRingCat.of K)).hom
        (VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
          (splitTorus.exponentCharacter _ I a) (RingCoordinates.testOver K K) t) * d)) := by
    rintro c rfl
    rw [charValue_underT]
    simp only [map_mul, Iso.hom_inv_id_apply]
    ring
  rw [rootPoint_rootMap, rootPoint_rootMap, hc _ rfl, key, key, conj_under Φ _ hΦ t d]

/-- **Torus equivariance.** If the field fibres are parametrized compatibly with `a`, the torus
acts on the root map through `a` on all points. -/
theorem rootMap_equivariant [IsReduced R] (a : I → ℤ)
    (hfield : ∀ (K : Type u) [Field K] [Algebra R K], ∃ (Φ : Ga K ≅ UK i mu nu K) (u0 : K),
      (∀ (Z : Over (Spec (CommRingCat.of K)))
        (t : Z ⟶ (splitTorus (Spec (CommRingCat.of K)) I).X) (x : Z ⟶ (Ga K).X),
        (t ≫ (tK i mu K).hom.hom) *
            (x ≫ (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)).hom.hom) *
            (t ≫ (tK i mu K).hom.hom)⁻¹ =
          VectorGroup.weightPointAction (splitTorus.exponentCharacter _ I a) Z t x ≫
            (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)).hom.hom) ∧
      fibreAlgHom i mu nu Φ K[X] Polynomial.X x = Polynomial.C u0 * Polynomial.X)
    (Z : Over (Spec (CommRingCat.of R))) (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X)
    (c : Γ(Z.left, ⊤)) :
    (t ≫ i.hom.hom) * rootPoint (rootMap i mu nu x hx hadd) Z c * (t ≫ i.hom.hom)⁻¹ =
      rootPoint (rootMap i mu nu x hx hadd) Z
        (VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
          (splitTorus.exponentCharacter _ I a) Z t * c) := by
  have hV : Smooth (Ga R).X.hom := Corepresented.smooth_groupScheme_iff.mpr inferInstance
  have : Smooth ((splitTorus (Spec (CommRingCat.of R)) I).X ⊗ (Ga R).X).hom :=
    smooth_tensor _ _ (smooth_splitTorus I) hV
  have : IsReduced ((splitTorus (Spec (CommRingCat.of R)) I).X ⊗ (Ga R).X).left :=
    Langlands.AlgebraicGeometry.SmoothReducedBase.isReduced_of_smooth_of_isReduced
      ((splitTorus (Spec (CommRingCat.of R)) I).X ⊗ (Ga R).X).hom
  have huniv : (fst (splitTorus (Spec (CommRingCat.of R)) I).X (Ga R).X ≫ i.hom.hom) *
      rootPoint (rootMap i mu nu x hx hadd) _
        ((VectorGroup.coordinates _ 1 _ (snd (splitTorus (Spec (CommRingCat.of R)) I).X
          (Ga R).X)).toAdd 0) *
      (fst (splitTorus (Spec (CommRingCat.of R)) I).X (Ga R).X ≫ i.hom.hom)⁻¹ =
      rootPoint (rootMap i mu nu x hx hadd) _
        (VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
          (splitTorus.exponentCharacter _ I a) _ (fst _ _) *
          (VectorGroup.coordinates _ 1 _ (snd (splitTorus (Spec (CommRingCat.of R)) I).X
            (Ga R).X)).toAdd 0) := by
    apply ext_of_fieldPoints
    intro K _ s w
    obtain ⟨_, rfl⟩ := exists_algebra_of_fieldPoint s
    obtain ⟨Φ, u0, hΦ, hψ⟩ := hfield K
    simp only [MonObj.comp_mul, GrpObj.comp_inv, comp_rootPoint, map_mul,
      ← VectorGroup.charValue_comp, ← Category.assoc]
    exact rootMap_equivariant_field i mu nu x hx hadd a Φ hΦ hψ _ _
  have h := congrArg (fun f => lift t (VectorGroup.scalarPoint _ Z c) ≫ f) huniv
  have hcX : (lift t (VectorGroup.scalarPoint _ Z c)).left.appTop
      ((VectorGroup.coordinates _ 1 _ (snd (splitTorus (Spec (CommRingCat.of R)) I).X
        (Ga R).X)).toAdd 0) = c := by
    have := congrFun (VectorGroup.coordinates_comp (lift t (VectorGroup.scalarPoint _ Z c))
      (snd (splitTorus (Spec (CommRingCat.of R)) I).X (Ga R).X)) 0
    rw [lift_snd, VectorGroup.coordinates_scalarPoint] at this
    exact this.symm
  simp only [MonObj.comp_mul, GrpObj.comp_inv, comp_rootPoint, map_mul,
    ← VectorGroup.charValue_comp, ← Category.assoc, lift_fst, hcX] at h
  exact h

end RootEquivariance

/-! ### The root map represents the root subgroup -/

section Represents

omit [IsAffineHom G.X.hom] [Fintype I] in
theorem appTop_appTop {T T' T'' : Over (Spec (CommRingCat.of R))} (a : T'' ⟶ T') (b : T' ⟶ T)
    (c : Γ(T.left, ⊤)) : a.left.appTop (b.left.appTop c) = (a ≫ b).left.appTop c := by
  rw [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

omit [IsAffineHom G.X.hom] in
/-- An equivariant map from `𝔾ₐ` takes values in the root subgroup. -/
theorem rootPoint_mem_subgroup {u : Ga R ⟶ G} (a : I → ℤ)
    (hequiv : ∀ (Z : Over (Spec (CommRingCat.of R)))
      (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (c : Γ(Z.left, ⊤)),
      (t ≫ i.hom.hom) * rootPoint u Z c * (t ≫ i.hom.hom)⁻¹ =
        rootPoint u Z (VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
          (splitTorus.exponentCharacter _ I a) Z t * c))
    {T : Over (Spec (CommRingCat.of R))} (c : Γ(T.left, ⊤)) :
    rootPoint u T c ∈ (RelativeRoot.subgroup (S := splitTorus.commGroupScheme _ I) i
      (splitTorus.exponentCharacter _ I a)).carrier T := by
  refine ⟨rootPoint u _ ((fst T (AffineLine.scheme _)).left.appTop c *
    AffineLine.homEquiv _ (snd T (AffineLine.scheme _))), ?_, ?_⟩
  · rw [RelativeRoot.IsOrbitExtension, comp_rootPoint, map_mul, appTop_appTop,
      ← AffineLine.homEquiv_comp, whiskerLeft_fst, whiskerLeft_snd, ← Category.assoc,
      AffineLine.homEquiv_comp_unitInclusion, RelativeRoot.orbit,
      AutomorphicAction.conjugation_act, comp_rootPoint]
    have h := hequiv _ (snd T (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I).X)
      ((fst T (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I).X).left.appTop c)
    rw [mul_comm] at h
    exact h.symm
  · rw [Dynamic.evalZero, comp_rootPoint, map_mul, ← AffineLine.homEquiv_comp, lift_snd,
      AffineLine.homEquiv_comp_zeroSection, mul_zero, rootPoint, scalarPoint_zero, MonObj.one_comp]

variable (x : coordU i mu nu)
  (hx : Function.Bijective (Polynomial.aeval x : R[X] →ₐ[R] coordU i mu nu))
  (hadd : ∀ (T : Over (Spec (CommRingCat.of R))) (y y' : T ⟶ (Uc i mu nu).X),
    coordX i mu nu x (y * y') = coordX i mu nu x y + coordX i mu nu x y')

omit [IsAffineHom G.X.hom] in
theorem subgroup_le_centralizer (a : I → ℤ) (ha0 : ∑ j, a j * mu j = 0) :
    RelativeRoot.subgroup (S := splitTorus.commGroupScheme _ I) i
        (splitTorus.exponentCharacter _ I a) ≤
      Dynamic.centralizer (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I mu) ≫ i) := by
  have hzero : splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I mu ≫
      splitTorus.exponentCharacter _ I a = 0 := by
    rw [splitTorus.exponentCocharacter_comp_exponentCharacter, ha0, Gm.powerHom_apply, zero_smul]
  exact (RelativeRoot.subgroup_le_kernelCentralizer (T := splitTorus.commGroupScheme _ I) i
    _).trans (RelativeRoot.kernelCentralizer_le_dynamicCentralizer_of_comp_eq_zero
      (T := splitTorus.commGroupScheme _ I) i _ _ hzero)

omit [IsAffineHom G.X.hom] in
theorem subgroup_le_unipotent (a : I → ℤ) {m : ℕ} (hm : 0 < m) (ham : ∑ j, a j * nu j = m) :
    RelativeRoot.subgroup (S := splitTorus.commGroupScheme _ I) i
        (splitTorus.exponentCharacter _ I a) ≤
      Dynamic.unipotent (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I nu) ≫ i) := by
  have hcomp : splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I nu ≫
      splitTorus.exponentCharacter _ I a = Gm.powerHom _ (m : ℤ) := by
    rw [splitTorus.exponentCocharacter_comp_exponentCharacter, ham]
  exact RelativeRoot.subgroup_le_dynamicUnipotent_of_power (S := splitTorus.commGroupScheme _ I)
    i _ _ hm hcomp

theorem exists_centralizer_point {T : Over (Spec (CommRingCat.of R))} {g : T ⟶ G.X}
    (hg : g ∈ (Dynamic.centralizer (CommGroupScheme.groupHom
      (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I mu) ≫ i)).carrier T) :
    ∃ z, z ≫ (jZ i mu).hom.hom = g ≫ (AffineCoordinates.groupSchemeIso G).inv.hom.hom := by
  have hC' := Dynamic.centralizer_le_comap (CommGroupScheme.groupHom
    (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I mu) ≫ i)
      (AffineCoordinates.groupSchemeIso G).inv T hg
  rw [SubgroupFunctor.mem_comap, Category.assoc, ← modelTorus, ← centCochar_eq] at hC'
  rw [← SubgroupFunctor.mem_range,
    (Corepresented.isRepresentedBy_centralizerHom (centCochar i mu)).2]
  exact hC'

theorem mem_unipotent_of {T : Over (Spec (CommRingCat.of R))} {g : T ⟶ G.X}
    (hg : g ∈ (Dynamic.unipotent (CommGroupScheme.groupHom
      (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I nu) ≫ i)).carrier T)
    {z : T ⟶ (Zc i mu).X}
    (hz : z ≫ (jZ i mu).hom.hom = g ≫ (AffineCoordinates.groupSchemeIso G).inv.hom.hom) :
    z ∈ (Dynamic.unipotent (unipCochar i mu nu)).carrier T := by
  have hU' := Dynamic.unipotent_le_comap (CommGroupScheme.groupHom
    (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I nu) ≫ i)
      (AffineCoordinates.groupSchemeIso G).inv T hg
  rw [SubgroupFunctor.mem_comap] at hU'
  rw [Dynamic.unipotent_eq_comap_of_isClosedSubgroup (unipCochar i mu nu) (jZ i mu)
    (Corepresented.isClosedSubgroup_centralizerHom _), SubgroupFunctor.mem_comap, hz]
  have e : unipCochar i mu nu ≫ jZ i mu =
      (CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I nu) ≫ i) ≫
        (AffineCoordinates.groupSchemeIso G).inv := by
    rw [unipCochar, Category.assoc, torusZ_comp, modelTorus, Category.assoc]
  rw [e]
  exact hU'

/-- Every point of the root subgroup lies in `U`, hence in the image of the root map. -/
theorem subgroup_le_range_rootMap (a : I → ℤ) (ha0 : ∑ j, a j * mu j = 0) {m : ℕ} (hm : 0 < m)
    (ham : ∑ j, a j * nu j = m) :
    RelativeRoot.subgroup (S := splitTorus.commGroupScheme _ I) i
        (splitTorus.exponentCharacter _ I a) ≤
      SubgroupFunctor.range (rootMap i mu nu x hx hadd) := by
  intro T g hg
  obtain ⟨z, hz⟩ := exists_centralizer_point i mu (subgroup_le_centralizer i mu a ha0 T hg)
  have hUz := mem_unipotent_of i mu nu (subgroup_le_unipotent i nu a hm ham T hg) hz
  obtain ⟨y, hy⟩ : ∃ y, y ≫ (jU i mu nu).hom.hom = z := by
    rw [← SubgroupFunctor.mem_range, (Corepresented.isRepresentedBy_unipotentHom _).2]
    exact hUz
  rw [SubgroupFunctor.mem_range]
  refine ⟨y ≫ (gaIsoU i mu nu x hx hadd).inv.hom.hom, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, rootMap, Iso.inv_hom_id_assoc, incl, Grp.comp_hom_hom,
    ← Category.assoc, hy, Grp.comp_hom_hom, ← Category.assoc, hz, Category.assoc,
    ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

/-- **The root map represents the root subgroup.** -/
theorem isRepresentedBy_rootMap (a : I → ℤ)
    (hequiv : ∀ (Z : Over (Spec (CommRingCat.of R)))
      (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (c : Γ(Z.left, ⊤)),
      (t ≫ i.hom.hom) * rootPoint (rootMap i mu nu x hx hadd) Z c * (t ≫ i.hom.hom)⁻¹ =
        rootPoint (rootMap i mu nu x hx hadd) Z
          (VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
            (splitTorus.exponentCharacter _ I a) Z t * c))
    (ha0 : ∑ j, a j * mu j = 0) {m : ℕ} (hm : 0 < m) (ham : ∑ j, a j * nu j = m) :
    (RelativeRoot.subgroup (S := splitTorus.commGroupScheme _ I) i
      (splitTorus.exponentCharacter _ I a)).IsRepresentedBy (rootMap i mu nu x hx hadd) := by
  refine ⟨?_, le_antisymm ?_ (subgroup_le_range_rootMap i mu nu x hx hadd a ha0 hm ham)⟩
  · have : IsClosedImmersion (rootMap i mu nu x hx hadd).hom.hom.left :=
      isClosedSubgroup_rootMap i mu nu x hx hadd
    exact Over.mono_of_mono_left _
  · rintro T g ⟨v, rfl⟩
    obtain ⟨c, rfl⟩ := (scalarPoint_bijective _ T).2 v
    exact rootPoint_mem_subgroup i a hequiv c

end Represents

/-! ### Root parametrizations from the field fibres -/

section Assembly

variable [Smooth G.X.hom] [IsLocalRing R] [IsReduced R]

/-- **Root parametrization over a reduced local ring.** Suppose `⟨a, mu⟩ = 0`, `⟨a, nu⟩ = m > 0`,
and on every field fibre the root group `U_K` is `𝔾ₐ` with the torus acting through `a`. Then
some `u : 𝔾ₐ ⟶ G` parametrizes the root group of `a` over `R`. -/
theorem exists_isRootParametrization (a : I → ℤ) (ha0 : ∑ j, a j * mu j = 0) {m : ℕ}
    (hm : 0 < m) (ham : ∑ j, a j * nu j = m)
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K], ∃ Φ : Ga K ≅ UK i mu nu K,
      ∀ (Z : Over (Spec (CommRingCat.of K)))
        (t : Z ⟶ (splitTorus (Spec (CommRingCat.of K)) I).X) (x : Z ⟶ (Ga K).X),
        (t ≫ (tK i mu K).hom.hom) *
            (x ≫ (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)).hom.hom) *
            (t ≫ (tK i mu K).hom.hom)⁻¹ =
          VectorGroup.weightPointAction (splitTorus.exponentCharacter _ I a) Z t x ≫
            (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)).hom.hom) :
    ∃ u : Ga R ⟶ G, IsRootParametrization i a u := by
  obtain ⟨x, hxm, hx⟩ := exists_coordinate i mu nu hm fun K _ _ => by
    obtain ⟨Φ, hΦ⟩ := hfib K
    exact ⟨_, Φ, hΦ, by rw [splitTorus.latticePairing_exponentCharacter_exponentCocharacter, ham]⟩
  have hline : ∀ (K : Type u) [Field K] [Algebra R K] (Φ : Ga K ≅ UK i mu nu K),
      (∀ (Z : Over (Spec (CommRingCat.of K)))
        (t : Z ⟶ (splitTorus (Spec (CommRingCat.of K)) I).X) (x : Z ⟶ (Ga K).X),
        (t ≫ (tK i mu K).hom.hom) *
            (x ≫ (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)).hom.hom) *
            (t ≫ (tK i mu K).hom.hom)⁻¹ =
          VectorGroup.weightPointAction (splitTorus.exponentCharacter _ I a) Z t x ≫
            (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)).hom.hom) →
      fibreAlgHom i mu nu Φ K[X] Polynomial.X x =
        Polynomial.C ((fibreAlgHom i mu nu Φ K[X] Polynomial.X x).coeff 1) * Polynomial.X := by
    intro K _ _ Φ hΦ
    ext j
    rw [Polynomial.coeff_C_mul_X]
    split_ifs with h
    · rw [h]
    · refine CommutativeAlgebra.GradedLine.coeff_eq_zero_of_scaling hm
        (scaling_fibre i mu nu Φ _ hΦ m (by
          rw [splitTorus.latticePairing_exponentCharacter_exponentCocharacter, ham])) _ x hxm j ?_
      intro h'
      apply h
      have hm' : (0 : ℤ) < m := by exact_mod_cast hm
      have : (j : ℤ) = 1 := by nlinarith
      exact_mod_cast this
  have hadd : ∀ (T : Over (Spec (CommRingCat.of R))) (y y' : T ⟶ (Uc i mu nu).X),
      coordX i mu nu x (y * y') = coordX i mu nu x y + coordX i mu nu x y' := by
    intro T y y'
    refine coordX_mul i mu nu x (fun K _ _ => ?_) y y'
    obtain ⟨Φ, hΦ⟩ := hfib K
    exact ⟨Φ, _, hline K Φ hΦ⟩
  have hequiv := rootMap_equivariant i mu nu x hx hadd a fun K _ _ => by
    obtain ⟨Φ, hΦ⟩ := hfib K
    exact ⟨Φ, _, hΦ, hline K Φ hΦ⟩
  exact ⟨rootMap i mu nu x hx hadd,
    { represents := isRepresentedBy_rootMap i mu nu x hx hadd a hequiv ha0 hm ham
      isClosedSubgroup := isClosedSubgroup_rootMap i mu nu x hx hadd
      equivariant := hequiv }⟩

end Assembly

/-! ### Root data: the choice of `mu` and `nu` -/

section RootDatum

variable {J : Type u} [Finite J] (P : RootDatum J (I → ℤ) (I → ℤ))

omit [IsAffineHom G.X.hom] in
/-- For a root `α₀` of a reduced root datum there is `mu ∈ ker α₀` such that the only roots
orthogonal to `mu` are `±α₀`. It is transported from the field statement
`RootReducedness.exists_cocharacter_pairing_eq_zero`. -/
theorem exists_kernel_exponent [P.IsReduced] (k : Type u) [Field k] (α₀ : J) :
    ∃ mu : I → ℤ, ∑ j, P.root α₀ j * mu j = 0 ∧
      ∀ β : J, ∑ j, P.root β j * mu j = 0 → P.root β = P.root α₀ ∨ P.root β = -P.root α₀ := by
  have hT : IsSplitTorus (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I).toGrp :=
    isSplitTorus_splitTorus I
  have hinj := LocalSplitBigCell.exponentCharacter_injective (I := I) k
  have hα : splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (P.root α₀) ≠ 0 := by
    intro h
    apply P.ne_zero α₀
    apply hinj
    rw [h, splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm I k, map_zero]
  obtain ⟨ζ, h0, hgen⟩ := RootReducedness.exists_cocharacter_pairing_eq_zero hT hα
    (Set.finite_range fun β => splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (P.root β))
  have hζ : splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I
      (splitTorus.cocharacterLatticeEquiv k I ζ) = ζ := by
    rw [splitTorus.exponentCocharacter_eq_cocharacterLatticeEquiv_symm, AddEquiv.symm_apply_apply]
  refine ⟨splitTorus.cocharacterLatticeEquiv k I ζ, ?_, fun β hβ => ?_⟩
  · rw [← splitTorus.latticePairing_exponentCharacter_exponentCocharacter I k, hζ, h0]
  · rw [← splitTorus.latticePairing_exponentCharacter_exponentCocharacter I k, hζ] at hβ
    have hdep := hgen _ ⟨β, rfl⟩ hβ
    have hdep' : ¬ LinearIndependent ℤ ![P.root α₀, P.root β] := by
      intro hli
      apply hdep
      rw [LinearIndependent.pair_iff] at hli ⊢
      intro s t hst
      apply hli s t
      apply hinj
      beta_reduce at hst
      rw [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm I k,
        splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm I k] at hst
      rw [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm I k, map_add, map_zsmul,
        map_zsmul, hst, splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm I k, map_zero]
    rcases RootPairing.IsReduced.eq_or_eq_neg (P := P) α₀ β hdep' with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h, neg_neg])

end RootDatum

/-! ### Root parametrizations for every root -/

omit [IsAffineHom G.X.hom] [Fintype I] in
/-- **Root parametrizations over a reduced local ring.** Let `R` be a reduced local ring, `G` a
reductive group over `R` with a split torus `i` that is maximal on every residue-field fibre, and
`P` a fibrewise root datum. Every root `α₀` of `P` has a root parametrization
`u : 𝔾ₐ ⟶ G` over `R`. It is constructed from the root group
`U_{Z_G(mu)}(nu)`, where `nu` is the coroot of `α₀` and `mu` is generic in the kernel of `α₀`. -/
theorem exists_rootParametrization {R : Type u} [CommRing R] [IsLocalRing R] [IsReduced R]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom] (hG : IsReductive G)
    {I : Type u} [Fintype I] (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)} (hP : IsFibrewiseRootDatumOf I G i P)
    (α₀ : J) : ∃ u : Ga R ⟶ G, IsRootParametrization i (P.root α₀) u := by
  have := hG.smooth
  have : Finite J := hP.finite
  have := hP.isReduced
  obtain ⟨mu, hmu0, hmu⟩ := exists_kernel_exponent P (IsLocalRing.ResidueField R) α₀
  have h2 : ∑ j, P.root α₀ j * P.coroot α₀ j = ((2 : ℕ) : ℤ) := by
    rw [← hP.pairing (IsLocalRing.ResidueField R), P.root_coroot_two]
    rfl
  refine exists_isRootParametrization i mu (P.coroot α₀) (P.root α₀) hmu0 two_pos h2
    fun K _ _ => ?_
  have hGK := hG.isConnectedReductive_baseChange (algebraBaseMap R K)
  have hmaxK := splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hmax K
  refine exists_fibreIso i mu (P.coroot α₀) K hGK hmaxK _ ((hP.mem_roots_iff K _).2 ⟨α₀, rfl⟩)
    ?_ ?_ ?_
  · intro β hβ hβ0
    obtain ⟨m, rfl⟩ : ∃ m, splitTorus.exponentCharacter (Spec (CommRingCat.of K)) I m = β :=
      ⟨splitTorus.characterLatticeEquiv K I β, by
        rw [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm,
          AddEquiv.symm_apply_apply]⟩
    obtain ⟨b, rfl⟩ := (hP.mem_roots_iff K m).1 hβ
    rw [splitTorus.latticePairing_exponentCharacter_exponentCocharacter] at hβ0
    rcases hmu b hβ0 with h | h
    · exact Or.inl (by rw [h])
    · refine Or.inr ?_
      rw [h, splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm,
        splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm, map_neg]
  · rw [splitTorus.latticePairing_exponentCharacter_exponentCocharacter, hmu0]
  · rw [splitTorus.latticePairing_exponentCharacter_exponentCocharacter, h2]
    norm_num

end Langlands.GroupScheme.LocalRootGroup
