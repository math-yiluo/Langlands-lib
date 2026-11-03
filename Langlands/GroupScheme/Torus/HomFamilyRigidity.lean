import Langlands.GroupScheme.Rational.TorusNormalizerRigidity

/-! # Rigidity of families of homomorphisms between split tori

Let `T ≅ 𝔾_m^I` and `D ≅ 𝔾_m^J` be split tori over a scheme `S`, and let `U` be a scheme over `S`.
A family of homomorphisms `T → D` parametrized by `U` assigns to every test scheme `V`, every
`a : V ⟶ U` and every torus point `t : V ⟶ T` a point `F V a t : V ⟶ D`, multiplicatively in `t`
and naturally in `V` (`IsHomFamily`). In unit coordinates such a family is a natural family of
maps `(I → Γ(V, 𝒪_V)ˣ) → (J → Γ(V, 𝒪_V)ˣ)` (`famUnits`).

Padding the coordinates of `J` with those of `I`, the family over an affine chart `Spec R ⟶ U` is
a `Langlands.GroupScheme.splitTorus.UnitsNatEnd R (I ⊕ J)` whose rows indexed by `I` are
constant (`chartFamily`). Its idempotent coefficients cut out, for each exponent matrix `m`, an
open and closed locus of points of `U` at which the family is the monomial map of `m`. Over a
connected `U` the family is therefore one monomial map (`exists_actsBy_of_connected`), so it does
not depend on the parameter (`eq_of_connected`, and the base-point form `eq_basePoint` over a
field).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace HomFamily

open splitTorus TorusConjugation

/-! ### Rectangular monomial maps -/

section Monomial

variable {I J : Type u} [Fintype I]

/-- The monomial map of a rectangular exponent matrix `m`: the `j`-th entry of the image of a
family of units `x` is `∏ i, x i ^ m j i`. -/
def rectPow {A : Type u} [CommRing A] (m : Matrix J I ℤ) (x : I → Aˣ) : J → Aˣ :=
  fun j => ∏ i, x i ^ m j i

theorem rectPow_map {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (m : Matrix J I ℤ)
    (x : I → Aˣ) :
    rectPow m (fun i => Units.map f.toMonoidHom (x i)) =
      fun j => Units.map f.toMonoidHom (rectPow m x j) := by
  funext j
  simp [rectPow, map_prod, map_zpow]

/-- The square exponent matrix on `I ⊕ J` whose rows indexed by `I` vanish and whose row
indexed by `j : J` is `m j` on `I` and zero on `J`. -/
def extMatrix (m : Matrix J I ℤ) : Matrix (I ⊕ J) (I ⊕ J) ℤ :=
  Matrix.of (Sum.elim (fun _ : I => (0 : I ⊕ J → ℤ)) (fun j => Sum.elim (m j) (0 : J → ℤ)))

variable [Fintype J]

/-- The monomial map of `extMatrix m` is `1` on `I` and the monomial map of `m` on `J`. -/
theorem powUnits_extMatrix {A : Type u} [CommRing A] (m : Matrix J I ℤ) (x : I ⊕ J → Aˣ) :
    powUnits (extMatrix m) x = Sum.elim (1 : I → Aˣ) (rectPow m fun i => x (Sum.inl i)) := by
  funext l
  cases l with
  | inl i => simp [powUnits, extMatrix]
  | inr j => simp [powUnits, extMatrix, rectPow, Fintype.prod_sum_type]

variable [DecidableEq I] [DecidableEq J]

/-- A natural endomorphism family on `I ⊕ J` that is `1` on `I` and only depends on the
coordinates in `I` is, over an integral domain, the monomial map of some `extMatrix m`. -/
theorem exists_extMatrix_coeff_eq_one {R : CommRingCat.{u}} (φ : UnitsNatEnd R (I ⊕ J))
    (h₁ : ∀ {A : CommRingCat.{u}} (α : R ⟶ A) (x : I ⊕ J → Aˣ) (i : I),
      φ.app α x (Sum.inl i) = 1)
    (h₂ : ∀ {A : CommRingCat.{u}} (α : R ⟶ A) (x : I ⊕ J → Aˣ),
      φ.app α x = φ.app α (Sum.elim (fun i => x (Sum.inl i)) 1))
    {K : CommRingCat.{u}} [IsDomain K] (β : R ⟶ K) :
    ∃ m : Matrix J I ℤ, ∀ l, β ((φ.coeffs l).coeff (extMatrix m l)) = 1 := by
  obtain ⟨M, hM⟩ := φ.exists_forall_coeff_eq_one β
  have hall := (φ.forall_app_eq_powUnits_iff β M).2 hM
  refine ⟨Matrix.of fun j i => M (Sum.inr j) (Sum.inl i),
    (φ.forall_app_eq_powUnits_iff β _).1 ?_⟩
  intro A f x
  rw [powUnits_extMatrix]
  funext l
  cases l with
  | inl i =>
    rw [h₁]
    rfl
  | inr j =>
    rw [h₂, hall]
    simp [powUnits, rectPow, Fintype.prod_sum_type]

end Monomial

/-! ### Families of homomorphisms -/

section Points

variable {S : Scheme.{u}} {T D : GroupScheme S} {U : Over S}

/-- `F` is a family of homomorphisms `T → D` parametrized by `U`: for each `a : V ⟶ U` the map
`F V a` on points over `V` is multiplicative, and the family is natural in the test scheme. -/
structure IsHomFamily (F : ∀ V : Over S, (V ⟶ U) → (V ⟶ T.X) → (V ⟶ D.X)) : Prop where
  map_mul : ∀ (V : Over S) (a : V ⟶ U) (t₁ t₂ : V ⟶ T.X), F V a (t₁ * t₂) = F V a t₁ * F V a t₂
  naturality : ∀ {V W : Over S} (f : W ⟶ V) (a : V ⟶ U) (t : V ⟶ T.X),
    F W (f ≫ a) (f ≫ t) = f ≫ F V a t

variable {I J : Type u} [Finite I] [Finite J] (eT : T ≅ splitTorus S I) (eD : D ≅ splitTorus S J)
  (F : ∀ V : Over S, (V ⟶ U) → (V ⟶ T.X) → (V ⟶ D.X))

/-- The family `F` in unit coordinates of the two split tori. -/
def famUnits {V : Over S} (a : V ⟶ U) (x : I → (Γ(V.left, ⊤))ˣ) : J → (Γ(V.left, ⊤))ˣ :=
  pointsEquiv J V (F V a ((pointsEquiv I V).symm x ≫ eT.inv.hom.hom) ≫ eD.hom.hom.hom)

/-- `F` is recovered from its unit coordinates. -/
theorem eq_famUnits {V : Over S} (a : V ⟶ U) (t : V ⟶ T.X) :
    F V a t = (pointsEquiv J V).symm (famUnits eT eD F a (pointsEquiv I V (t ≫ eT.hom.hom.hom)))
      ≫ eD.inv.hom.hom := by
  rw [famUnits, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, Category.assoc t,
    ← Grp.comp_hom_hom eT.hom eT.inv, eT.hom_inv_id, Grp.id_hom_hom, Category.comp_id,
    Category.assoc, ← Grp.comp_hom_hom eD.hom eD.inv, eD.hom_inv_id, Grp.id_hom_hom,
    Category.comp_id]

/-- `famUnits` only depends on the underlying morphism of schemes. -/
theorem famUnits_congr {X : Scheme.{u}} {s₁ s₂ : X ⟶ S} (b₁ : Over.mk s₁ ⟶ U)
    (b₂ : Over.mk s₂ ⟶ U) (h : b₁.left = b₂.left) :
    famUnits eT eD F b₁ = famUnits eT eD F b₂ := by
  have hs : s₁ = s₂ := by
    have h₁ := Over.w b₁
    have h₂ := Over.w b₂
    simp only [Over.mk_hom] at h₁ h₂
    rw [← h₁, ← h₂, h]
  subst hs
  have : b₁ = b₂ := Over.OverMorphism.ext h
  subst this
  rfl

variable {F} (hF : IsHomFamily F)
include hF

theorem famUnits_mul {V : Over S} (a : V ⟶ U) (x y : I → (Γ(V.left, ⊤))ˣ) :
    famUnits eT eD F a (x * y) = famUnits eT eD F a x * famUnits eT eD F a y := by
  simp only [famUnits, map_mul, MonObj.mul_comp, hF.map_mul]

theorem famUnits_naturality {V V' : Over S} (c : V' ⟶ V) (a : V ⟶ U)
    (x : I → (Γ(V.left, ⊤))ˣ) :
    famUnits eT eD F (c ≫ a) (unitsRestrict I c x) = unitsRestrict J c (famUnits eT eD F a x) := by
  rw [famUnits, famUnits, ← comp_pointsEquiv_symm, Category.assoc, hF.naturality,
    Category.assoc, pointsEquiv_naturality]

omit hF

variable [Fintype I]

variable (F) in
/-- The family acts by the monomial map of the exponent matrix `m` over every test scheme over
`V`. -/
def ActsBy (m : Matrix J I ℤ) {V : Over S} (a : V ⟶ U) : Prop :=
  ∀ (V' : Over S) (c : V' ⟶ V) (x : I → (Γ(V'.left, ⊤))ˣ),
    famUnits eT eD F (c ≫ a) x = rectPow m x

theorem ActsBy.comp {m : Matrix J I ℤ} {V V' : Over S} {a : V ⟶ U}
    (h : ActsBy eT eD F m a) (c : V' ⟶ V) : ActsBy eT eD F m (c ≫ a) := by
  intro W d x
  rw [← Category.assoc]
  exact h W (d ≫ c) x

variable (F) in
theorem actsBy_congr (m : Matrix J I ℤ) {X : Scheme.{u}} {s₁ s₂ : X ⟶ S}
    (b₁ : Over.mk s₁ ⟶ U) (b₂ : Over.mk s₂ ⟶ U) (h : b₁.left = b₂.left) :
    ActsBy eT eD F m b₁ ↔ ActsBy eT eD F m b₂ := by
  have hs : s₁ = s₂ := by
    have h₁ := Over.w b₁
    have h₂ := Over.w b₂
    simp only [Over.mk_hom] at h₁ h₂
    rw [← h₁, ← h₂, h]
  subst hs
  have : b₁ = b₂ := Over.OverMorphism.ext h
  subst this
  rfl

variable (F) in
/-- The family acts by `m` on the torus over the residue field at `x`. -/
def ActsAtPoint (m : Matrix J I ℤ) (x : U.left) : Prop :=
  ActsBy eT eD F m (overHom (U := U) (U.left.fromSpecResidueField x))

include hF in
/-- It suffices to test the action on affine test schemes. -/
theorem actsBy_of_forall_affine (m : Matrix J I ℤ) {V : Over S} (a : V ⟶ U)
    (h : ∀ (A : CommRingCat.{u}) (s : Spec A ⟶ S) (b : Over.mk s ⟶ V)
      (x : I → (Γ(Spec A, ⊤))ˣ), famUnits eT eD F (b ≫ a) x = rectPow m x) :
    ActsBy eT eD F m a := by
  intro V' c x
  apply (pointsEquiv J V').symm.injective
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext V'.left.affineOpenCover.openCover _ _ fun j => ?_
  let d : Over.mk (V'.left.affineOpenCover.f j ≫ V'.hom) ⟶ V' :=
    Over.homMk (V'.left.affineOpenCover.f j)
  have key : d ≫ (pointsEquiv J V').symm (famUnits eT eD F (c ≫ a) x) =
      d ≫ (pointsEquiv J V').symm (rectPow m x) := by
    rw [comp_pointsEquiv_symm, comp_pointsEquiv_symm, ← famUnits_naturality eT eD hF,
      ← Category.assoc, h _ _ (d ≫ c)]
    congr 1
    exact rectPow_map d.left.appTop.hom m x
  exact congrArg (fun f => f.left) key

/-! ### Affine charts -/

variable {R : CommRingCat.{u}} {s : Spec R ⟶ S}

include hF

omit [Fintype I] in
/-- The family through a chart `ρ : Spec R ⟶ U`, in unit coordinates over the rings under `R`,
padded to a natural endomorphism family on `I ⊕ J` that is `1` on `I`. -/
def chartFamily (ρ : Over.mk s ⟶ U) : UnitsNatEnd R (I ⊕ J) where
  app {A} α x := Sum.elim 1 fun j => specUnits A (famUnits eT eD F (chartPoint ρ α)
    (fun l => (specUnits A).symm (x (Sum.inl l))) j)
  app_mul {A} α x y := by
    funext l
    cases l with
    | inl i => simp
    | inr j =>
      have hxy : (fun l => (specUnits A).symm (x (Sum.inl l) * y (Sum.inl l))) =
          (fun l => (specUnits A).symm (x (Sum.inl l))) *
            (fun l => (specUnits A).symm (y (Sum.inl l))) := by
        funext l
        simp
      simp only [Sum.elim_inr, Pi.mul_apply]
      rw [hxy, famUnits_mul eT eD hF, Pi.mul_apply, map_mul]
  naturality {A B} α f x := by
    funext l
    cases l with
    | inl i => simp
    | inr j =>
      have hx : (fun l => (specUnits B).symm
          ((fun l' => Units.map f.hom.toMonoidHom (x l')) (Sum.inl l))) =
          unitsRestrict I (chartMap (s := s) α f) (fun l => (specUnits A).symm (x (Sum.inl l))) := by
        funext l
        apply (specUnits B).injective
        rw [MulEquiv.apply_symm_apply]
        change _ = specUnits B (Units.map (Spec.map f).appTop.hom.toMonoidHom
          ((specUnits A).symm (x (Sum.inl l))))
        rw [specUnits_naturality, MulEquiv.apply_symm_apply]
      change specUnits B (famUnits eT eD F (chartPoint ρ (α ≫ f)) _ j) = _
      rw [hx, ← chartMap_comp_chartPoint, famUnits_naturality eT eD hF]
      change specUnits B (Units.map (Spec.map f).appTop.hom.toMonoidHom _) = _
      rw [specUnits_naturality]
      rfl

omit [Fintype I] in
theorem chartFamily_app_inl (ρ : Over.mk s ⟶ U) {A : CommRingCat.{u}} (α : R ⟶ A)
    (x : I ⊕ J → Aˣ) (i : I) : (chartFamily eT eD hF ρ).app α x (Sum.inl i) = 1 :=
  rfl

omit [Fintype I] in
theorem chartFamily_app_eq (ρ : Over.mk s ⟶ U) {A : CommRingCat.{u}} (α : R ⟶ A)
    (x : I ⊕ J → Aˣ) :
    (chartFamily eT eD hF ρ).app α x =
      (chartFamily eT eD hF ρ).app α (Sum.elim (fun i => x (Sum.inl i)) 1) :=
  rfl

variable [Fintype J] [DecidableEq I] [DecidableEq J]

theorem actsBy_chartPoint_iff (ρ : Over.mk s ⟶ U) {B : CommRingCat.{u}} (β : R ⟶ B)
    (m : Matrix J I ℤ) :
    ActsBy eT eD F m (chartPoint ρ β) ↔
      ∀ l, β (((chartFamily eT eD hF ρ).coeffs l).coeff (extMatrix m l)) = 1 := by
  rw [← UnitsNatEnd.forall_app_eq_powUnits_iff]
  constructor
  · intro h A f x
    have h' := h _ (chartMap (s := s) β f) (fun l => (specUnits A).symm (x (Sum.inl l)))
    rw [chartMap_comp_chartPoint] at h'
    rw [powUnits_extMatrix]
    funext l
    cases l with
    | inl i => rfl
    | inr j =>
      change specUnits A (famUnits eT eD F (chartPoint ρ (β ≫ f)) _ j) = _
      rw [h']
      simp [rectPow, map_prod, map_zpow]
  · intro h
    apply actsBy_of_forall_affine eT eD hF
    intro A s' b x
    let f : B ⟶ A := Spec.preimage b.left
    have hb : b.left = Spec.map f := (Spec.map_preimage b.left).symm
    rw [famUnits_congr eT eD F (b ≫ chartPoint ρ β) (chartPoint ρ (β ≫ f))
      (by simp [chartPoint, hb, Spec.map_comp])]
    have hj := congrFun (h A f (Sum.elim (fun l => specUnits A (x l)) 1))
    funext j
    apply (specUnits A).injective
    have hj' := hj (Sum.inr j)
    simp only [chartFamily, Sum.elim_inr, Sum.elim_inl, MulEquiv.symm_apply_apply,
      powUnits_extMatrix] at hj'
    rw [hj']
    simp [rectPow, map_prod, map_zpow]

theorem actsBy_chart_iff (ρ : Over.mk s ⟶ U) (m : Matrix J I ℤ) :
    ActsBy eT eD F m ρ ↔ ∀ l, ((chartFamily eT eD hF ρ).coeffs l).coeff (extMatrix m l) = 1 := by
  rw [actsBy_congr eT eD F m ρ (chartPoint ρ (𝟙 R)) (by simp [chartPoint]),
    actsBy_chartPoint_iff eT eD hF]
  simp

/-! ### Points -/

theorem actsBy_overHom_iff {K : Type u} [Field K] (y : Spec (CommRingCat.of K) ⟶ U.left)
    (m : Matrix J I ℤ) :
    ActsBy eT eD F m (overHom (U := U) y) ↔
      ActsAtPoint eT eD F m (y (IsLocalRing.closedPoint K)) := by
  let ψ := Scheme.descResidueField (Scheme.stalkClosedPointTo y)
  have hy : Spec.map ψ ≫ U.left.fromSpecResidueField (y (IsLocalRing.closedPoint K)) = y :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K U.left y
  let ρ := overHom (U := U) (U.left.fromSpecResidueField (y (IsLocalRing.closedPoint K)))
  rw [actsBy_congr eT eD F m (overHom (U := U) y) (chartPoint ρ ψ) (by simp [chartPoint, ρ, hy]),
    actsBy_chartPoint_iff eT eD hF, ActsAtPoint, actsBy_chart_iff eT eD hF]
  refine forall_congr' fun l => ⟨fun h => ψ.hom.injective (by rw [h, map_one]), fun h => ?_⟩
  rw [h, map_one]

theorem actsAtPoint_chart_iff (ρ : Over.mk s ⟶ U) (m : Matrix J I ℤ) (p : PrimeSpectrum R) :
    ActsAtPoint eT eD F m (ρ.left p) ↔
      ∀ l, ((chartFamily eT eD hF ρ).coeffs l).coeff (extMatrix m l) ∉ p.asIdeal := by
  let β : R ⟶ CommRingCat.of p.asIdeal.ResidueField :=
    CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField)
  have hβ : (Spec.map β) (IsLocalRing.closedPoint p.asIdeal.ResidueField) = p := by
    have h := PrimeSpectrum.residueField_comap p
    have hmem : PrimeSpectrum.comap (algebraMap R p.asIdeal.ResidueField)
        (IsLocalRing.closedPoint p.asIdeal.ResidueField) ∈ ({p} : Set (PrimeSpectrum R)) :=
      h ▸ ⟨_, rfl⟩
    exact hmem
  have hpt : (Spec.map β ≫ ρ.left) (IsLocalRing.closedPoint p.asIdeal.ResidueField) =
      ρ.left p := by
    rw [Scheme.Hom.comp_apply, hβ]
    rfl
  rw [← hpt, ← actsBy_overHom_iff eT eD hF,
    actsBy_congr eT eD F m (overHom (U := U) (Spec.map β ≫ ρ.left)) (chartPoint ρ β) rfl,
    actsBy_chartPoint_iff eT eD hF]
  exact forall_congr' fun l => algebraMap_residueField_eq_one_iff
    ((chartFamily eT eD hF ρ).isIdempotentElem_coeff l (extMatrix m l)) p.asIdeal

/-- The locus where the family acts by `m` is open and closed. -/
theorem isLocallyConstant_actsAtPoint (m : Matrix J I ℤ) :
    IsLocallyConstant (ActsAtPoint eT eD F m) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  obtain ⟨k, p₀, hp₀⟩ : ∃ k p₀, U.left.affineOpenCover.f k p₀ = x :=
    ⟨_, U.left.affineOpenCover.covers x⟩
  subst hp₀
  let b := U.left.affineOpenCover.f k
  let ρ := overHom (U := U) b
  let c : I ⊕ J → U.left.affineOpenCover.X k :=
    fun l => ((chartFamily eT eD hF ρ).coeffs l).coeff (extMatrix m l)
  let P : PrimeSpectrum (U.left.affineOpenCover.X k) → Prop :=
    fun p => ∀ l, c l ∉ p.asIdeal
  have hP : ∀ p, ActsAtPoint eT eD F m (b p) ↔ P p :=
    fun p => actsAtPoint_chart_iff eT eD hF ρ m p
  have hopen : IsOpen {p | P p ↔ P p₀} := by
    by_cases h0 : P p₀
    · have hset : {p | P p ↔ P p₀} = ⋂ l, (PrimeSpectrum.basicOpen (c l) : Set _) := by
        ext p
        simp [P, h0]
      rw [hset]
      exact isOpen_iInter_of_finite fun l => (PrimeSpectrum.basicOpen (c l)).isOpen
    · have hset : {p | P p ↔ P p₀} = ⋃ l, (PrimeSpectrum.basicOpen (1 - c l) : Set _) := by
        ext p
        simp only [Set.mem_ofPred_eq, h0, iff_false, P, not_forall, not_not, Set.mem_iUnion,
          SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
        exact exists_congr fun l => mem_iff_one_sub_notMem
          ((chartFamily eT eD hF ρ).isIdempotentElem_coeff l (extMatrix m l)) p.asIdeal
      rw [hset]
      exact isOpen_iUnion fun l => (PrimeSpectrum.basicOpen (1 - c l)).isOpen
  refine ⟨b '' {p | P p ↔ P p₀}, b.isOpenEmbedding.isOpenMap _ hopen, ⟨p₀, Iff.rfl, rfl⟩, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  exact propext ((hP p).trans (hp.trans (hP p₀).symm))

theorem actsAtPoint_of_preconnected [PreconnectedSpace U.left] (m : Matrix J I ℤ) {x₀ : U.left}
    (h₀ : ActsAtPoint eT eD F m x₀) (x : U.left) : ActsAtPoint eT eD F m x := by
  rw [(isLocallyConstant_actsAtPoint eT eD hF m).apply_eq_of_preconnectedSpace x x₀]
  exact h₀

/-- If the family acts by `m` at every point, it acts by `m` over every test scheme. -/
theorem actsBy_of_forall_actsAtPoint (m : Matrix J I ℤ) (h : ∀ x, ActsAtPoint eT eD F m x) :
    ActsBy eT eD F m (𝟙 U) := by
  apply actsBy_of_forall_affine eT eD hF
  intro A s' b x
  have hd : ∀ l, ((chartFamily eT eD hF b).coeffs l).coeff (extMatrix m l) = 1 := by
    intro l
    have hu : IsUnit (((chartFamily eT eD hF b).coeffs l).coeff (extMatrix m l)) := by
      by_contra hd
      obtain ⟨P, hP, hdP⟩ := exists_max_ideal_of_mem_nonunits hd
      exact (actsAtPoint_chart_iff eT eD hF b m ⟨P, hP.isPrime⟩).1 (h _) l hdP
    have hid := (chartFamily eT eD hF b).isIdempotentElem_coeff l (extMatrix m l)
    exact hu.mul_left_cancel (by rw [hid.eq, mul_one])
  have hb := (actsBy_chart_iff eT eD hF b m).2 hd _ (𝟙 _) x
  rw [Category.id_comp] at hb
  rw [Category.comp_id]
  exact hb

/-- Over a residue field the family is a monomial map. -/
theorem exists_actsAtPoint (x : U.left) : ∃ m, ActsAtPoint eT eD F m x := by
  let ρ := overHom (U := U) (U.left.fromSpecResidueField x)
  obtain ⟨m, hm⟩ := exists_extMatrix_coeff_eq_one (chartFamily eT eD hF ρ)
    (chartFamily_app_inl eT eD hF ρ) (chartFamily_app_eq eT eD hF ρ) (𝟙 _)
  exact ⟨m, (actsBy_chart_iff eT eD hF ρ m).2 hm⟩

/-- **Rigidity.** Over a connected parameter scheme the family is the monomial map of one
exponent matrix. -/
theorem exists_actsBy_of_connected [ConnectedSpace U.left] :
    ∃ m : Matrix J I ℤ, ActsBy eT eD F m (𝟙 U) := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty U.left)
  obtain ⟨m, hm⟩ := exists_actsAtPoint eT eD hF x₀
  exact ⟨m, actsBy_of_forall_actsAtPoint eT eD hF m
    (actsAtPoint_of_preconnected eT eD hF m hm)⟩

end Points

/-! ### Independence of the parameter -/

/-- **Rigidity of families of homomorphisms of split tori** (after Milne, *Algebraic Groups*,
Theorem 12.36). Let `T` and `D` be split tori over a scheme `S` and let `U` be a scheme over `S`
whose underlying space is connected. A family `F` of homomorphisms `T → D` parametrized by `U`,
multiplicative in the torus point and natural in the test scheme, does not depend on the
parameter: `F V a t = F V a' t` for all `a a' : V ⟶ U`. -/
theorem eq_of_connected {S : Scheme.{u}} {T D : GroupScheme S} (hT : IsSplitTorus T)
    (hD : IsSplitTorus D) {U : Over S} [ConnectedSpace U.left]
    (F : ∀ V : Over S, (V ⟶ U) → (V ⟶ T.X) → (V ⟶ D.X))
    (hmul : ∀ (V : Over S) (a : V ⟶ U) (t₁ t₂ : V ⟶ T.X),
      F V a (t₁ * t₂) = F V a t₁ * F V a t₂)
    (hnat : ∀ {V W : Over S} (f : W ⟶ V) (a : V ⟶ U) (t : V ⟶ T.X),
      F W (f ≫ a) (f ≫ t) = f ≫ F V a t)
    {V : Over S} (a a' : V ⟶ U) (t : V ⟶ T.X) : F V a t = F V a' t := by
  classical
  obtain ⟨I, hI, ⟨eT⟩⟩ := hT
  obtain ⟨J, hJ, ⟨eD⟩⟩ := hD
  let _ : Fintype I := Fintype.ofFinite I
  let _ : Fintype J := Fintype.ofFinite J
  have hF : IsHomFamily F := ⟨hmul, hnat⟩
  obtain ⟨m, hm⟩ := exists_actsBy_of_connected eT eD hF
  have key : ∀ b : V ⟶ U, F V b t = (pointsEquiv J V).symm
      (rectPow m (pointsEquiv I V (t ≫ eT.hom.hom.hom))) ≫ eD.inv.hom.hom := by
    intro b
    have hb := hm V b (pointsEquiv I V (t ≫ eT.hom.hom.hom))
    rw [Category.comp_id] at hb
    rw [eq_famUnits eT eD F b t, hb]
  rw [key a, key a']

/-- **Base-point form over a field.** Over `Spec k`, a family of homomorphisms between split tori
parametrized by a connected scheme `U` with a `k`-point `u₀` agrees, at every parameter, with the
homomorphism at `u₀`. -/
theorem eq_basePoint {k : Type u} [Field k] {T D : GroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T) (hD : IsSplitTorus D) {U : Over (Spec (CommRingCat.of k))}
    [ConnectedSpace U.left] (u₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U)
    (F : ∀ V : Over (Spec (CommRingCat.of k)), (V ⟶ U) → (V ⟶ T.X) → (V ⟶ D.X))
    (hmul : ∀ (V : Over (Spec (CommRingCat.of k))) (a : V ⟶ U) (t₁ t₂ : V ⟶ T.X),
      F V a (t₁ * t₂) = F V a t₁ * F V a t₂)
    (hnat : ∀ {V W : Over (Spec (CommRingCat.of k))} (f : W ⟶ V) (a : V ⟶ U) (t : V ⟶ T.X),
      F W (f ≫ a) (f ≫ t) = f ≫ F V a t)
    (V : Over (Spec (CommRingCat.of k))) (a : V ⟶ U) (t : V ⟶ T.X) :
    F V a t = F V ((Over.homMk V.hom (by simp) : V ⟶ Over.mk (𝟙 _)) ≫ u₀) t :=
  eq_of_connected hT hD F hmul hnat a _ t

end HomFamily

end Langlands.GroupScheme
