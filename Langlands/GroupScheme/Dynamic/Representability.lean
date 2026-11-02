import Langlands.GroupScheme.Dynamic.AffineExtension
import Langlands.GroupScheme.CorepresentedClosedSubgroup

/-! # Representability of dynamic subgroups of affine group schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AffineLine

section LaurentRange

variable {A : Type u} [CommRing A]

theorem coeff_toLaurent_natCast (p : Polynomial A) (m : ℕ) :
    (Polynomial.toLaurent p).coeff (m : ℤ) = p.coeff m := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective _ m

theorem coeff_toLaurent_of_neg (p : Polynomial A) {n : ℤ} (hn : n < 0) :
    (Polynomial.toLaurent p).coeff n = 0 := by
  rw [LaurentPolynomial.coeff_toLaurent]
  refine Finsupp.mapDomain_of_notMem_range _ _ ?_
  rintro ⟨m, hm⟩
  have : (0 : ℤ) ≤ n := by rw [← hm]; exact Int.natCast_nonneg m
  omega

theorem coeff_trunc (q : LaurentPolynomial A) (m : ℕ) :
    (LaurentPolynomial.trunc q).coeff m = q.coeff (m : ℤ) :=
  rfl

/-- A Laurent polynomial without terms of negative degree is a polynomial. -/
theorem toLaurent_trunc {q : LaurentPolynomial A} (hq : ∀ n < 0, q.coeff n = 0) :
    Polynomial.toLaurent (LaurentPolynomial.trunc q) = q := by
  ext n
  rcases lt_or_ge n 0 with hn | hn
  · rw [coeff_toLaurent_of_neg _ hn, hq n hn]
  · lift n to ℕ using hn
    rw [coeff_toLaurent_natCast, coeff_trunc]

end LaurentRange

section PolynomialLift

variable {A C : CommRingCat.{u}}

/-- A ring homomorphism `C ⟶ A[X, X⁻¹]` whose values have no terms of negative degree, as a ring
homomorphism `C ⟶ A[X]`. -/
def polynomialLift (g : C ⟶ CommRingCat.of (LaurentPolynomial A))
    (hg : ∀ c, ∀ n < 0, (g c).coeff n = 0) : C ⟶ CommRingCat.of (Polynomial A) :=
  CommRingCat.ofHom
    { toFun := fun c => LaurentPolynomial.trunc (g c)
      map_one' := Polynomial.toLaurent_injective (by
        rw [toLaurent_trunc (hg 1), map_one, map_one])
      map_mul' := fun c c' => Polynomial.toLaurent_injective (by
        rw [toLaurent_trunc (hg _), map_mul, map_mul, toLaurent_trunc (hg c),
          toLaurent_trunc (hg c')])
      map_zero' := by rw [map_zero, map_zero]
      map_add' := fun c c' => by rw [map_add, map_add] }

theorem polynomialLift_comp (g : C ⟶ CommRingCat.of (LaurentPolynomial A))
    (hg : ∀ c, ∀ n < 0, (g c).coeff n = 0) :
    polynomialLift g hg ≫ polynomialToLaurent A = g :=
  CommRingCat.hom_ext (RingHom.ext fun c => toLaurent_trunc (hg c))

/-- Morphisms from `Spec A[X]` to an affine scheme agree when they agree on
`Spec A[X, X⁻¹]`. -/
theorem specMap_polynomialToLaurent_cancel {D : CommRingCat.{u}}
    {v w : Spec (CommRingCat.of (Polynomial A)) ⟶ Spec D}
    (h : Spec.map (polynomialToLaurent A) ≫ v = Spec.map (polynomialToLaurent A) ≫ w) :
    v = w := by
  rw [← Spec.map_preimage v, ← Spec.map_preimage w] at h ⊢
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun d =>
    Polynomial.toLaurent_injective (congrArg (fun φ => φ.hom d) h'))

end PolynomialLift

end AffineLine

namespace Corepresented

open AffineLine

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  {e : (F ⋙ forget GrpCat).CorepresentableBy B}

section Coaction

variable (e) in
/-- The structure morphism `Spec B ⟶ Spec R` of the affine group scheme `Spec B`. -/
abbrev structureMap : Spec (CommRingCat.of B) ⟶ Spec R :=
  (groupScheme F e).X.hom

variable (e) in
/-- The universal point of `Spec B`: the identity of `Spec B` over `Spec R`. -/
def universalPoint : Over.mk (structureMap e) ⟶ (groupScheme F e).X :=
  Over.homMk (𝟙 _) (Category.id_comp _)

variable {A : CommRingCat.{u}} {f : Spec A ⟶ Spec R}

/-- The ring map `B ⟶ A` classifying a point of `Spec B` over `Spec A`. -/
abbrev pointRing (x : Over.mk f ⟶ (groupScheme F e).X) : CommRingCat.of B ⟶ A :=
  Spec.preimage (R := CommRingCat.of B) x.left

/-- Every point over `Spec A` is the pullback of the universal point. -/
theorem homMk_comp_universalPoint (x : Over.mk f ⟶ (groupScheme F e).X) :
    (Over.homMk x.left (Over.w x) : Over.mk f ⟶ Over.mk (structureMap e)) ≫
      universalPoint e = x :=
  Over.OverMorphism.ext (Category.comp_id x.left)

variable (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e)

/-- The coaction `B ⟶ B[T, T⁻¹]` of `𝔾_m` on `Spec B` by conjugation through `χ`: the ring map
of the orbit map `Spec B[T, T⁻¹] ⟶ Spec B` of the universal point. -/
def coaction : CommRingCat.of B ⟶ CommRingCat.of (LaurentPolynomial (CommRingCat.of B)) :=
  Spec.preimage (R := CommRingCat.of B)
    (laurentPoint (structureMap e) ≫ Dynamic.orbit χ (universalPoint e)).left

theorem specMap_coaction :
    Spec.map (coaction χ) = (laurentPoint (structureMap e) ≫ Dynamic.orbit χ (universalPoint e)).left :=
  Spec.map_preimage _

/-- The orbit map on `Spec A[T, T⁻¹]` of a point `x` over `Spec A` is the spectrum of the
coaction followed by the coefficient map of `x`. -/
theorem laurentPoint_comp_orbit_left (x : Over.mk f ⟶ (groupScheme F e).X) :
    (laurentPoint f ≫ Dynamic.orbit χ x).left =
      Spec.map (coaction χ ≫ laurentCoeffMap (pointRing x)) := by
  have h := laurentPoint_comp_whiskerRight
    (Over.homMk x.left (Over.w x) : Over.mk f ⟶ Over.mk (structureMap e))
  have h3 := congrArg (fun y => laurentPoint f ≫ Dynamic.orbit χ y) (homMk_comp_universalPoint x)
  have h2 : laurentPoint f ≫ Dynamic.orbit χ x =
      laurentMap (Over.homMk x.left (Over.w x)) ≫ laurentPoint (structureMap e) ≫
        Dynamic.orbit χ (universalPoint e) := by
    rw [← h3, ← Dynamic.whiskerRight_orbit, reassoc_of% h]
    rfl
  rw [h2, Spec.map_comp, specMap_coaction]
  rfl

theorem coeff_laurentCoeffMap_coaction (x : Over.mk f ⟶ (groupScheme F e).X) (b : B) (n : ℤ) :
    (laurentCoeffMap (pointRing x) (coaction χ b)).coeff n = pointRing x ((coaction χ b).coeff n) :=
  AddMonoidAlgebra.coeff_mapRingHom _ _ _

end Coaction

section Points

variable {A : CommRingCat.{u}} {f : Spec A ⟶ Spec R}

theorem specMap_pointRing (x : Over.mk f ⟶ (groupScheme F e).X) :
    Spec.map (pointRing x) = x.left :=
  Spec.map_preimage _

/-- Points over `Spec A` are determined by their classifying ring maps. -/
theorem hom_ext_of_pointRing {x y : Over.mk f ⟶ (groupScheme F e).X}
    (h : pointRing x = pointRing y) : x = y := by
  apply Over.OverMorphism.ext
  rw [← specMap_pointRing x, ← specMap_pointRing y, h]

/-- The classifying ring map of a point over `Spec A` is an `R`-algebra map. -/
theorem algebraMap_comp_pointRing (x : Over.mk f ⟶ (groupScheme F e).X) :
    CommRingCat.ofHom (algebraMap R B) ≫ pointRing x = Spec.preimage f := by
  apply Spec.map_injective
  rw [Spec.map_comp, specMap_pointRing, Spec.map_preimage]
  exact Over.w x

variable (e) in
/-- The counit `B ⟶ R` of the Hopf algebra `B`: the ring map classifying the identity point of
`Spec B` over `Spec R`. -/
def counit : CommRingCat.of B ⟶ R :=
  pointRing (1 : Over.mk (𝟙 (Spec R)) ⟶ (groupScheme F e).X)

/-- The identity point over `Spec A` is classified by the counit followed by `R ⟶ A`. -/
theorem pointRing_one : pointRing (1 : Over.mk f ⟶ (groupScheme F e).X) =
    counit e ≫ Spec.preimage f := by
  have h : (Over.homMk f (Category.comp_id f) : Over.mk f ⟶ Over.mk (𝟙 (Spec R))) ≫
      (1 : Over.mk (𝟙 (Spec R)) ⟶ (groupScheme F e).X) = 1 :=
    MonObj.comp_one _
  apply Spec.map_injective
  rw [specMap_pointRing, Spec.map_comp, counit, specMap_pointRing, Spec.map_preimage, ← h]
  rfl

theorem appTop_ΓSpecIso_inv_of_specMap_eq {A' D : CommRingCat.{u}} (φ : D ⟶ A')
    (y : Spec A' ⟶ Spec D) (hy : Spec.map φ = y) (d : D) :
    y.appTop ((Scheme.ΓSpecIso D).inv d) = (Scheme.ΓSpecIso A').inv (φ d) := by
  subst hy
  exact (congrArg (fun ψ => ψ.hom d) (Scheme.ΓSpecIso_inv_naturality φ)).symm

/-- On global sections, a point over `Spec A` pulls back `b ∈ B` to its image under the
classifying ring map. -/
theorem appTop_ΓSpecIso_inv (x : Over.mk f ⟶ (groupScheme F e).X) (b : B) :
    x.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) =
      (Scheme.ΓSpecIso A).inv (pointRing x b) :=
  appTop_ΓSpecIso_inv_of_specMap_eq (pointRing x) x.left (specMap_pointRing x) b

/-- On every test scheme, the algebra map classifying a point is the pullback of functions along
the point. -/
theorem homEquiv_symm_pointsEquiv_apply (T : Over (Spec R)) (x : T ⟶ (groupScheme F e).X)
    (b : B) :
    (e.homEquiv.symm (pointsEquiv F e T x)).hom b =
      x.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) := by
  rw [pointsEquiv_apply, Equiv.symm_apply_apply]
  change T ⟶ (algSpec R).obj (op B) at x
  rw [Adjunction.homEquiv_counit]
  rfl

end Points

section Reduction

variable (K : SubgroupFunctor (groupScheme F e)) (I : Ideal B)

variable (e) in
/-- `K` is cut out by the ideal `I` on affine test schemes: a point over `Spec A` lies in `K`
exactly when its classifying ring map `B ⟶ A` vanishes on `I`. -/
def IsAffineCutOutBy : Prop :=
  ∀ (A : CommRingCat.{u}) (f : Spec A ⟶ Spec R) (x : Over.mk f ⟶ (groupScheme F e).X),
    x ∈ K.carrier (Over.mk f) ↔ ∀ b ∈ I, pointRing x b = 0

/-- The subgroups of the groups `F A` given by the points of `K` over `Spec A`. -/
def affineSubgroups (A : CommAlgCat.{u} R) : Subgroup (F.obj A) :=
  (K.carrier ((algSpec R).obj (op A))).comap (affinePointsEquiv F e A).symm.toMonoidHom

variable {K I}

theorem pointRing_algSpecMap {A : CommAlgCat.{u} R} (φ : B ⟶ A) (b : B) :
    pointRing (F := F) (e := e) (f := ((algSpec R).obj (op A)).hom) ((algSpec R).map φ.op) b =
      φ b := by
  have h : pointRing (F := F) (e := e) (f := ((algSpec R).obj (op A)).hom)
      ((algSpec R).map φ.op) = CommRingCat.ofHom (φ.hom : B →+* A) :=
    Spec.map_injective ((specMap_pointRing _).trans rfl)
  rw [h]
  rfl

theorem isCutOutBy_affineSubgroups (hK : IsAffineCutOutBy e K I) :
    IsCutOutBy e (affineSubgroups K) I := by
  intro A x
  obtain ⟨φ, rfl⟩ := e.homEquiv.surjective x
  have hx : (affinePointsEquiv F e A).symm (e.homEquiv φ) = (algSpec R).map φ.op :=
    (affinePointsEquiv F e A).symm_apply_eq.2 (affinePointsEquiv_map F e A φ).symm
  change (affinePointsEquiv F e A).symm (e.homEquiv φ) ∈ K.carrier ((algSpec R).obj (op A)) ↔ _
  rw [hx, Equiv.symm_apply_apply]
  refine (hK (CommRingCat.of A) ((algSpec R).obj (op A)).hom ((algSpec R).map φ.op)).trans ?_
  exact forall₂_congr fun b _ => iff_of_eq (congrArg (· = 0) (pointRing_algSpecMap φ b))

variable (hK : IsAffineCutOutBy e K I)

/-- The inclusion `Spec (B ⧸ I) ⟶ Spec B` is a point of `K`. -/
theorem cutHom_mem :
    (cutHom (isCutOutBy_affineSubgroups hK)).hom.hom ∈
      K.carrier (cutGroupScheme (isCutOutBy_affineSubgroups hK)).X := by
  refine (hK (CommRingCat.of (quotientAlgebra I))
    (cutGroupScheme (isCutOutBy_affineSubgroups hK)).X.hom _).2 fun b hb => ?_
  have h : pointRing (F := F) (e := e) (f := (cutGroupScheme (isCutOutBy_affineSubgroups hK)).X.hom)
      (A := CommRingCat.of (quotientAlgebra I)) (cutHom (isCutOutBy_affineSubgroups hK)).hom.hom =
        CommRingCat.ofHom (Ideal.Quotient.mk I) :=
    Spec.map_injective ((specMap_pointRing _).trans (cutHom_left _))
  rw [h]
  exact Ideal.Quotient.eq_zero_iff_mem.2 hb

/-- A subgroup functor cut out by `I` on affine test schemes is cut out by `I` on all test
schemes. -/
theorem cutSubgroupFunctor_affineSubgroups :
    cutSubgroupFunctor (isCutOutBy_affineSubgroups hK) = K := by
  ext T x
  constructor
  · intro hx
    rw [← range_cutHom (isCutOutBy_affineSubgroups hK)] at hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    exact K.comp_mem y (cutHom_mem hK)
  · intro hx
    rw [mem_cutSubgroupFunctor, isCutOutBy_affineSubgroups hK]
    intro b hb
    rw [homEquiv_symm_pointsEquiv_apply]
    refine T.left.affineOpenCover.openCover.ext_elem _ _ fun k => ?_
    have hk := K.comp_mem (Over.homMk (T.left.affineOpenCover.f k) rfl :
      Over.mk (T.left.affineOpenCover.f k ≫ T.hom) ⟶ T) hx
    have h0 := (hK _ _ _).1 hk b hb
    have h1 := appTop_ΓSpecIso_inv (Over.homMk (T.left.affineOpenCover.f k) rfl ≫ x :
      Over.mk (T.left.affineOpenCover.f k ≫ T.hom) ⟶ _) b
    rw [h0, map_zero] at h1
    exact h1.trans (map_zero _).symm

/-- A subgroup functor cut out by `I` on affine test schemes is represented by the closed
subgroup scheme `Spec (B ⧸ I)`. -/
theorem isRepresentedBy_cutHom_affineSubgroups :
    K.IsRepresentedBy (cutHom (isCutOutBy_affineSubgroups hK)) := by
  have h := isRepresentedBy_cutHom (isCutOutBy_affineSubgroups hK)
  rwa [cutSubgroupFunctor_affineSubgroups hK] at h

end Reduction

section Extension

variable (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e) {A : CommRingCat.{u}}
  {f : Spec A ⟶ Spec R}

theorem coeff_laurentCoeffMap {A' : CommRingCat.{u}} (ψ : A' ⟶ A) (q : LaurentPolynomial A')
    (n : ℤ) : (laurentCoeffMap ψ q).coeff n = ψ (q.coeff n) :=
  AddMonoidAlgebra.coeff_mapRingHom _ _ _

theorem laurentCoeffMap_C {A' : CommRingCat.{u}} (ψ : A' ⟶ A) (a : A') :
    laurentCoeffMap ψ (LaurentPolynomial.C a) = LaurentPolynomial.C (ψ a) := by
  simp only [CommRingCat.hom_ofHom, ← LaurentPolynomial.single_eq_C,
    AddMonoidAlgebra.mapRingHom_single]

/-- A ring map `θ : B ⟶ A[X]` lifting the coaction composed with the classifying map of `x`
defines a morphism `Spec A[X] ⟶ Spec B` over `Spec R`. -/
def polynomialExtension (x : Over.mk f ⟶ (groupScheme F e).X)
    (θ : CommRingCat.of B ⟶ CommRingCat.of (Polynomial A))
    (hθ : θ ≫ polynomialToLaurent A = coaction χ ≫ laurentCoeffMap (pointRing x)) :
    polynomialScheme f ⟶ (groupScheme F e).X :=
  Over.homMk (Spec.map θ) (by
    apply specMap_polynomialToLaurent_cancel
    have h1 : Spec.map (polynomialToLaurent A) ≫ Spec.map θ =
        (laurentPoint f ≫ Dynamic.orbit χ x).left := by
      rw [← Spec.map_comp, hθ, laurentPoint_comp_orbit_left]
    exact ((reassoc_of% h1) (groupScheme F e).X.hom).trans
      (Over.w (laurentPoint f ≫ Dynamic.orbit χ x)))

variable {χ}

theorem laurentInclusion_comp_polynomialExtension (x : Over.mk f ⟶ (groupScheme F e).X)
    (θ : CommRingCat.of B ⟶ CommRingCat.of (Polynomial A))
    (hθ : θ ≫ polynomialToLaurent A = coaction χ ≫ laurentCoeffMap (pointRing x)) :
    laurentInclusion f ≫ polynomialExtension χ x θ hθ = laurentPoint f ≫ Dynamic.orbit χ x := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, laurentPoint_comp_orbit_left, ← hθ, Spec.map_comp]
  rfl

theorem pointRing_polynomialExtension (x : Over.mk f ⟶ (groupScheme F e).X)
    (θ : CommRingCat.of B ⟶ CommRingCat.of (Polynomial A))
    (hθ : θ ≫ polynomialToLaurent A = coaction χ ≫ laurentCoeffMap (pointRing x)) :
    pointRing (polynomialExtension χ x θ hθ) = θ :=
  Spec.preimage_map θ

/-- The classifying ring map of an extension along `Spec A[X, X⁻¹] ⊆ Spec A[X]` of the orbit map
of `x` lifts the coaction composed with the classifying map of `x`. -/
theorem pointRing_comp_polynomialToLaurent {x : Over.mk f ⟶ (groupScheme F e).X}
    {E : polynomialScheme f ⟶ (groupScheme F e).X}
    (h : laurentInclusion f ≫ E = laurentPoint f ≫ Dynamic.orbit χ x) :
    pointRing E ≫ polynomialToLaurent A = coaction χ ≫ laurentCoeffMap (pointRing x) := by
  apply Spec.map_injective
  rw [Spec.map_comp, specMap_pointRing, ← laurentPoint_comp_orbit_left, ← h]
  rfl

theorem pointRing_polynomialZero_comp (E : polynomialScheme f ⟶ (groupScheme F e).X) :
    pointRing (polynomialZero f ≫ E) = pointRing E ≫ polynomialEvalZero A := by
  apply Spec.map_injective
  rw [specMap_pointRing, Spec.map_comp, specMap_pointRing]
  rfl

theorem laurentPoint_comp_fst_comp_left (x : Over.mk f ⟶ (groupScheme F e).X) :
    (laurentPoint f ≫ fst (Over.mk f) (Gm (Spec R)).X ≫ x).left =
      Spec.map (pointRing x ≫ polynomialC A ≫ polynomialToLaurent A) := by
  rw [laurentPoint, lift_fst_assoc, Spec.map_comp, Spec.map_comp, specMap_pointRing]
  rfl

end Extension

section Membership

variable (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e) {A : CommRingCat.{u}}
  {f : Spec A ⟶ Spec R}

/-- A point over `Spec A` lies in `P_G(χ)` exactly when its classifying ring map kills the
coefficients of negative degree of the coaction. -/
theorem mem_parabolic_iff (x : Over.mk f ⟶ (groupScheme F e).X) :
    x ∈ (Dynamic.parabolic χ).carrier (Over.mk f) ↔
      ∀ b, ∀ n < 0, pointRing x ((coaction χ b).coeff n) = 0 := by
  constructor
  · rintro ⟨E, hE⟩ b n hn
    have h := pointRing_comp_polynomialToLaurent (laurentInclusion_comp_of_whiskerLeft f hE)
    rw [← coeff_laurentCoeffMap_coaction, ← CommRingCat.comp_apply, ← h, CommRingCat.comp_apply]
    exact coeff_toLaurent_of_neg _ hn
  · intro h
    have hL : ∀ b, ∀ n < 0, ((coaction χ ≫ laurentCoeffMap (pointRing x)) b).coeff n = 0 :=
      fun b n hn => (coeff_laurentCoeffMap_coaction χ x b n).trans (h b n hn)
    exact ⟨polynomialPointInv f ≫ polynomialExtension χ x _ (polynomialLift_comp _ hL),
      whiskerLeft_comp_of_laurentInclusion f (laurentInclusion_comp_polynomialExtension x _ _)⟩

theorem pointRing_coeff_coaction_sub_C (x : Over.mk f ⟶ (groupScheme F e).X) (b : B) (n : ℤ) :
    pointRing x ((coaction χ b - (LaurentPolynomial.C b : LaurentPolynomial (CommRingCat.of B))).coeff n) =
      (laurentCoeffMap (pointRing x) (coaction χ b) - LaurentPolynomial.C (pointRing x b)).coeff n := by
  rw [← laurentCoeffMap_C, ← map_sub, coeff_laurentCoeffMap]

/-- A point over `Spec A` lies in `Z_G(χ)` exactly when its classifying ring map kills the
coefficients of `c(b) - b` for the coaction `c` and all `b ∈ B`. -/
theorem mem_centralizer_iff (x : Over.mk f ⟶ (groupScheme F e).X) :
    x ∈ (Dynamic.centralizer χ).carrier (Over.mk f) ↔
      ∀ b n, pointRing x
        ((coaction χ b - (LaurentPolynomial.C b : LaurentPolynomial (CommRingCat.of B))).coeff n) =
          0 := by
  rw [Dynamic.mem_centralizer]
  have key : Dynamic.orbit χ x = fst (Over.mk f) (Gm (Spec R)).X ≫ x ↔
      coaction χ ≫ laurentCoeffMap (pointRing x) =
        pointRing x ≫ polynomialC A ≫ polynomialToLaurent A := by
    constructor
    · intro h
      apply Spec.map_injective
      rw [← laurentPoint_comp_orbit_left, ← laurentPoint_comp_fst_comp_left, h]
    · intro h
      have h' : laurentPoint f ≫ Dynamic.orbit χ x =
          laurentPoint f ≫ fst (Over.mk f) (Gm (Spec R)).X ≫ x :=
        Over.OverMorphism.ext (by
          rw [laurentPoint_comp_orbit_left, laurentPoint_comp_fst_comp_left, h])
      have h'' := congrArg (laurentPointInv f ≫ ·) h'
      simpa only [reassoc_of% (laurentPointInv_comp_laurentPoint f)] using h''
  rw [key]
  constructor
  · intro h b n
    rw [pointRing_coeff_coaction_sub_C, ← CommRingCat.comp_apply, h]
    simp
  · intro h
    refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
    have hb : laurentCoeffMap (pointRing x) (coaction χ b) -
        LaurentPolynomial.C (pointRing x b) = 0 :=
      LaurentPolynomial.ext fun n => by
        rw [← pointRing_coeff_coaction_sub_C, h b n]
        rfl
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
      Polynomial.toLaurent_C]
    exact sub_eq_zero.1 hb

/-- A point over `Spec A` lies in `U_G(χ)` exactly when its classifying ring map kills the
coefficients of negative degree of the coaction, and the constant coefficient of `c(b)` agrees
with the counit `ε(b)`. -/
theorem mem_unipotent_iff (x : Over.mk f ⟶ (groupScheme F e).X) :
    x ∈ (Dynamic.unipotent χ).carrier (Over.mk f) ↔
      (∀ b, ∀ n < 0, pointRing x ((coaction χ b).coeff n) = 0) ∧
        ∀ b, pointRing x ((coaction χ b).coeff 0 - algebraMap R B (counit e b)) = 0 := by
  constructor
  · rintro ⟨E, hE, hE0⟩
    refine ⟨(mem_parabolic_iff χ x).1 ⟨E, hE⟩, fun b => ?_⟩
    have hθ := pointRing_comp_polynomialToLaurent (laurentInclusion_comp_of_whiskerLeft f hE)
    have h0 : polynomialZero f ≫ polynomialPoint f ≫ E = 1 := by
      rw [← evalZero_polynomialPointInv, ← Category.assoc,
        polynomialPointInv_comp_polynomialPoint, Category.id_comp, hE0]
    have h1 := congrArg pointRing h0
    rw [pointRing_polynomialZero_comp, pointRing_one] at h1
    have h2 := congrArg (fun φ => φ b) h1
    rw [map_sub, sub_eq_zero]
    calc pointRing x ((coaction χ b).coeff 0)
        = (Polynomial.toLaurent (pointRing (polynomialPoint f ≫ E) b)).coeff ((0 : ℕ) : ℤ) := by
          rw [← coeff_laurentCoeffMap_coaction, ← CommRingCat.comp_apply, ← hθ]
          rfl
      _ = (pointRing (polynomialPoint f ≫ E) b).eval 0 := by
          rw [coeff_toLaurent_natCast, Polynomial.coeff_zero_eq_eval_zero]
      _ = Spec.preimage f (counit e b) := h2
      _ = pointRing x (algebraMap R B (counit e b)) := by
          rw [← algebraMap_comp_pointRing x]
          rfl
  · rintro ⟨hP, h0⟩
    have hL : ∀ b, ∀ n < 0, ((coaction χ ≫ laurentCoeffMap (pointRing x)) b).coeff n = 0 :=
      fun b n hn => (coeff_laurentCoeffMap_coaction χ x b n).trans (hP b n hn)
    refine ⟨polynomialPointInv f ≫ polynomialExtension χ x _ (polynomialLift_comp _ hL),
      whiskerLeft_comp_of_laurentInclusion f (laurentInclusion_comp_polynomialExtension x _ _), ?_⟩
    rw [evalZero_polynomialPointInv]
    apply hom_ext_of_pointRing
    rw [pointRing_polynomialZero_comp, pointRing_polynomialExtension, pointRing_one]
    refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
    have hb := h0 b
    rw [map_sub, sub_eq_zero] at hb
    calc (polynomialLift _ hL ≫ polynomialEvalZero A).hom b
        = (LaurentPolynomial.trunc (laurentCoeffMap (pointRing x) (coaction χ b))).coeff 0 :=
          (Polynomial.coeff_zero_eq_eval_zero _).symm
      _ = pointRing x ((coaction χ b).coeff 0) := coeff_laurentCoeffMap_coaction χ x b 0
      _ = pointRing x (algebraMap R B (counit e b)) := hb
      _ = (counit e ≫ Spec.preimage f).hom b := by
          rw [← algebraMap_comp_pointRing x]
          rfl

end Membership

section Ideals

theorem forall_mem_span_iff {A : CommRingCat.{u}} (ψ : CommRingCat.of B ⟶ A) (s : Set B) :
    (∀ b ∈ Ideal.span s, ψ b = 0) ↔ ∀ b ∈ s, ψ b = 0 := by
  refine ⟨fun h b hb => h b (Ideal.subset_span hb), fun h => ?_⟩
  have hle : Ideal.span s ≤ RingHom.ker ψ.hom :=
    Ideal.span_le.2 fun b hb => RingHom.mem_ker.2 (h b hb)
  exact fun b hb => RingHom.mem_ker.1 (hle hb)

variable (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e)

/-- The ideal of `B` generated by the coefficients of negative degree of the coaction
`c : B ⟶ B[T, T⁻¹]`. -/
def parabolicIdeal : Ideal B :=
  Ideal.span {d | ∃ b, ∃ n < 0, (coaction χ b).coeff n = d}

/-- The ideal of `B` generated by the coefficients of `c(b) - b` for the coaction
`c : B ⟶ B[T, T⁻¹]` and all `b ∈ B`. -/
def centralizerIdeal : Ideal B :=
  Ideal.span {d | ∃ b n,
    (coaction χ b - (LaurentPolynomial.C b : LaurentPolynomial (CommRingCat.of B))).coeff n = d}

/-- The ideal of `B` generated by the coefficients of negative degree of the coaction
`c : B ⟶ B[T, T⁻¹]` and by the differences between the constant coefficient of `c(b)` and the
counit `ε(b)`. -/
def unipotentIdeal : Ideal B :=
  Ideal.span ({d | ∃ b, ∃ n < 0, (coaction χ b).coeff n = d} ∪
    {d | ∃ b, (coaction χ b).coeff 0 - algebraMap R B (counit e b) = d})

theorem isAffineCutOutBy_parabolic :
    IsAffineCutOutBy e (Dynamic.parabolic χ) (parabolicIdeal χ) := by
  intro A f x
  rw [mem_parabolic_iff, parabolicIdeal, forall_mem_span_iff]
  exact ⟨fun h _ ⟨b, n, hn, hd⟩ => hd ▸ h b n hn, fun h b n hn => h _ ⟨b, n, hn, rfl⟩⟩

theorem isAffineCutOutBy_centralizer :
    IsAffineCutOutBy e (Dynamic.centralizer χ) (centralizerIdeal χ) := by
  intro A f x
  rw [mem_centralizer_iff, centralizerIdeal, forall_mem_span_iff]
  exact ⟨fun h _ ⟨b, n, hd⟩ => hd ▸ h b n, fun h b n => h _ ⟨b, n, rfl⟩⟩

theorem isAffineCutOutBy_unipotent :
    IsAffineCutOutBy e (Dynamic.unipotent χ) (unipotentIdeal χ) := by
  intro A f x
  rw [mem_unipotent_iff, unipotentIdeal, forall_mem_span_iff]
  constructor
  · rintro ⟨hP, h0⟩ d (⟨b, n, hn, rfl⟩ | ⟨b, rfl⟩)
    · exact hP b n hn
    · exact h0 b
  · intro h
    exact ⟨fun b n hn => h _ (Or.inl ⟨b, n, hn, rfl⟩), fun b => h _ (Or.inr ⟨b, rfl⟩)⟩

end Ideals

section Schemes

variable (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e)

/-- The dynamic parabolic subgroup scheme `P_G(χ)` of `G = Spec B`: the spectrum of
`B ⧸ parabolicIdeal χ`. -/
abbrev parabolicScheme : GroupScheme (Spec R) :=
  cutGroupScheme (isCutOutBy_affineSubgroups (isAffineCutOutBy_parabolic χ))

/-- The centralizer subgroup scheme `Z_G(χ)` of `G = Spec B`: the spectrum of
`B ⧸ centralizerIdeal χ`. -/
abbrev centralizerScheme : GroupScheme (Spec R) :=
  cutGroupScheme (isCutOutBy_affineSubgroups (isAffineCutOutBy_centralizer χ))

/-- The dynamic unipotent subgroup scheme `U_G(χ)` of `G = Spec B`: the spectrum of
`B ⧸ unipotentIdeal χ`. -/
abbrev unipotentScheme : GroupScheme (Spec R) :=
  cutGroupScheme (isCutOutBy_affineSubgroups (isAffineCutOutBy_unipotent χ))

/-- The inclusion `P_G(χ) ⟶ G`, a closed immersion. -/
abbrev parabolicHom : parabolicScheme χ ⟶ groupScheme F e :=
  cutHom _

/-- The inclusion `Z_G(χ) ⟶ G`, a closed immersion. -/
abbrev centralizerHom : centralizerScheme χ ⟶ groupScheme F e :=
  cutHom _

/-- The inclusion `U_G(χ) ⟶ G`, a closed immersion. -/
abbrev unipotentHom : unipotentScheme χ ⟶ groupScheme F e :=
  cutHom _

theorem isRepresentedBy_parabolicHom :
    (Dynamic.parabolic χ).IsRepresentedBy (parabolicHom χ) :=
  isRepresentedBy_cutHom_affineSubgroups (isAffineCutOutBy_parabolic χ)

theorem isRepresentedBy_centralizerHom :
    (Dynamic.centralizer χ).IsRepresentedBy (centralizerHom χ) :=
  isRepresentedBy_cutHom_affineSubgroups (isAffineCutOutBy_centralizer χ)

theorem isRepresentedBy_unipotentHom :
    (Dynamic.unipotent χ).IsRepresentedBy (unipotentHom χ) :=
  isRepresentedBy_cutHom_affineSubgroups (isAffineCutOutBy_unipotent χ)

theorem isClosedSubgroup_parabolicHom : IsClosedSubgroup (parabolicHom χ) :=
  isClosedSubgroup_cutHom _

theorem isClosedSubgroup_centralizerHom : IsClosedSubgroup (centralizerHom χ) :=
  isClosedSubgroup_cutHom _

theorem isClosedSubgroup_unipotentHom : IsClosedSubgroup (unipotentHom χ) :=
  isClosedSubgroup_cutHom _

end Schemes

end Corepresented

end Langlands.GroupScheme
