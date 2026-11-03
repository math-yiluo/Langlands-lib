import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Torus.UnitsNaturalEndomorphism

/-! # Rigidity of conjugation by torus-normalizing points

Let `i : T ⟶ G` be a monomorphism from a split torus `T ≅ 𝔾_m^I` over a scheme `S`, and let `g`
be a point of the normalizer `torusNormalizer i` over a test scheme `U`. Conjugation by `g`
sends torus points over every `V ⟶ U` to torus points; in unit coordinates this is a natural
family of endomorphisms of `I → Γ(V, 𝒪_V)ˣ`, written `conjUnits`.

For an exponent matrix `m`, the locus of points `x ∈ U` at which conjugation by `g` acts on the
torus over the residue field `κ(x)` by the monomial map of `m` is open and closed. On an affine
chart `Spec R ⟶ U` it is cut out by the idempotent coefficients of
`Langlands.GroupScheme.splitTorus.UnitsNatEnd`. If the locus is all of `U`, conjugation by `g`
acts by `m` over every test scheme. Consequently, over a connected `U`, conjugation by `g` acts
through one automorphism `σ` of `T` over `S` (`exists_isNormalizingAut_of_connected`), and `g`
centralizes the torus as soon as it does so at one point.

Over a field `k`, restriction `N(k)/Z(k) → N(U)/Z(U)` is injective for every test scheme `U`
with a point (`relativeWeylGroupRestrict_injective`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace TorusConjugation

open splitTorus

section Points

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S} (i : T.toGrp ⟶ G)
  {I : Type u} [Finite I] (e : T.toGrp ≅ splitTorus S I)

/-- Pulling back a family of unit coordinates commutes with the point model of the split
torus. -/
theorem comp_pointsEquiv_symm {V V' : Over S} (c : V' ⟶ V) (x : I → (Γ(V.left, ⊤))ˣ) :
    c ≫ (pointsEquiv I V).symm x = (pointsEquiv I V').symm (unitsRestrict I c x) := by
  apply (pointsEquiv I V').injective
  rw [pointsEquiv_naturality, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

/-- The point of `G` given by the torus point with unit coordinates `x`. -/
def unitsPoint (V : Over S) (x : I → (Γ(V.left, ⊤))ˣ) : V ⟶ G.X :=
  ((pointsEquiv I V).symm x ≫ e.inv.hom.hom) ≫ i.hom.hom

theorem unitsPoint_mul (V : Over S) (x y : I → (Γ(V.left, ⊤))ˣ) :
    unitsPoint i e V (x * y) = unitsPoint i e V x * unitsPoint i e V y := by
  simp only [unitsPoint, map_mul, MonObj.mul_comp]

theorem comp_unitsPoint {V V' : Over S} (c : V' ⟶ V) (x : I → (Γ(V.left, ⊤))ˣ) :
    c ≫ unitsPoint i e V x = unitsPoint i e V' (unitsRestrict I c x) := by
  rw [unitsPoint, unitsPoint, ← Category.assoc, ← Category.assoc, comp_pointsEquiv_symm]

/-- Every torus point is a point with unit coordinates. -/
theorem comp_eq_unitsPoint (V : Over S) (t : V ⟶ T.X) :
    t ≫ i.hom.hom = unitsPoint i e V (pointsEquiv I V (t ≫ e.hom.hom.hom)) := by
  rw [unitsPoint, MulEquiv.symm_apply_apply, Category.assoc t, ← Grp.comp_hom_hom e.hom e.inv,
    e.hom_inv_id, Grp.id_hom_hom, Category.comp_id]

theorem unitsPoint_injective [Mono i.hom.hom.left] (V : Over S) :
    Function.Injective (unitsPoint i e V) := by
  intro x y h
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : IsIso e.inv.hom.hom :=
    (inferInstance : IsIso ((Grp.forget (Over S)).mapIso e.symm).hom)
  rw [unitsPoint, unitsPoint, cancel_mono, cancel_mono] at h
  exact (pointsEquiv I V).symm.injective h

variable {i} {U : Over S} {g : U ⟶ G.X}

theorem exists_conj_unitsPoint (hg : g ∈ (torusNormalizer i).carrier U) {V : Over S}
    (a : V ⟶ U) (x : I → (Γ(V.left, ⊤))ˣ) :
    ∃ y, (a ≫ g) * unitsPoint i e V x * (a ≫ g)⁻¹ = unitsPoint i e V y := by
  obtain ⟨⟨t, ht⟩, -⟩ :=
    (mem_torusNormalizer i).1 hg V a ((pointsEquiv I V).symm x ≫ e.inv.hom.hom)
  exact ⟨_, ht.trans (comp_eq_unitsPoint i e V t)⟩

variable (hg : g ∈ (torusNormalizer i).carrier U)

/-- The unit coordinates of the conjugate by `a ≫ g` of the torus point with coordinates
`x`. -/
def conjUnits {V : Over S} (a : V ⟶ U) (x : I → (Γ(V.left, ⊤))ˣ) : I → (Γ(V.left, ⊤))ˣ :=
  (exists_conj_unitsPoint e hg a x).choose

theorem conjUnits_spec {V : Over S} (a : V ⟶ U) (x : I → (Γ(V.left, ⊤))ˣ) :
    (a ≫ g) * unitsPoint i e V x * (a ≫ g)⁻¹ = unitsPoint i e V (conjUnits e hg a x) :=
  (exists_conj_unitsPoint e hg a x).choose_spec

/-- `conjUnits` only depends on the underlying morphism of schemes. -/
theorem conjUnits_congr {X : Scheme.{u}} {s₁ s₂ : X ⟶ S} (b₁ : Over.mk s₁ ⟶ U)
    (b₂ : Over.mk s₂ ⟶ U) (h : b₁.left = b₂.left) : conjUnits e hg b₁ = conjUnits e hg b₂ := by
  have hs : s₁ = s₂ := by
    have h₁ := Over.w b₁
    have h₂ := Over.w b₂
    simp only [Over.mk_hom] at h₁ h₂
    rw [← h₁, ← h₂, h]
  subst hs
  have : b₁ = b₂ := Over.OverMorphism.ext h
  subst this
  rfl

variable [Mono i.hom.hom.left]

theorem conjUnits_eq_iff {V : Over S} (a : V ⟶ U) (x y : I → (Γ(V.left, ⊤))ˣ) :
    conjUnits e hg a x = y ↔ (a ≫ g) * unitsPoint i e V x * (a ≫ g)⁻¹ = unitsPoint i e V y := by
  rw [conjUnits_spec e hg a x, (unitsPoint_injective i e V).eq_iff]

theorem conjUnits_mul {V : Over S} (a : V ⟶ U) (x y : I → (Γ(V.left, ⊤))ˣ) :
    conjUnits e hg a (x * y) = conjUnits e hg a x * conjUnits e hg a y := by
  rw [conjUnits_eq_iff, unitsPoint_mul, unitsPoint_mul, ← conjUnits_spec, ← conjUnits_spec]
  group

theorem conjUnits_naturality {V V' : Over S} (c : V' ⟶ V) (a : V ⟶ U)
    (x : I → (Γ(V.left, ⊤))ˣ) :
    conjUnits e hg (c ≫ a) (unitsRestrict I c x) = unitsRestrict I c (conjUnits e hg a x) := by
  rw [conjUnits_eq_iff, ← comp_unitsPoint, ← comp_unitsPoint, ← conjUnits_spec]
  simp only [MonObj.comp_mul, GrpObj.comp_inv, Category.assoc]

/-- Conjugation by `g` acts by the monomial map of the exponent matrix `m` on the torus points
over every test scheme over `V`. -/
def ActsBy [Fintype I] (m : Matrix I I ℤ) {V : Over S} (a : V ⟶ U) : Prop :=
  ∀ (V' : Over S) (c : V' ⟶ V) (x : I → (Γ(V'.left, ⊤))ˣ),
    conjUnits e hg (c ≫ a) x = powUnits m x

variable [Fintype I]

omit [Mono i.hom.hom.left] in
theorem ActsBy.comp {m : Matrix I I ℤ} {V V' : Over S} {a : V ⟶ U} (h : ActsBy e hg m a)
    (c : V' ⟶ V) : ActsBy e hg m (c ≫ a) := by
  intro W d x
  rw [← Category.assoc]
  exact h W (d ≫ c) x

omit [Mono i.hom.hom.left] in
theorem actsBy_congr (m : Matrix I I ℤ) {X : Scheme.{u}} {s₁ s₂ : X ⟶ S}
    (b₁ : Over.mk s₁ ⟶ U) (b₂ : Over.mk s₂ ⟶ U) (h : b₁.left = b₂.left) :
    ActsBy e hg m b₁ ↔ ActsBy e hg m b₂ := by
  have hs : s₁ = s₂ := by
    have h₁ := Over.w b₁
    have h₂ := Over.w b₂
    simp only [Over.mk_hom] at h₁ h₂
    rw [← h₁, ← h₂, h]
  subst hs
  have : b₁ = b₂ := Over.OverMorphism.ext h
  subst this
  rfl

/-- Acting by the identity matrix is centralizing the torus. -/
theorem actsBy_one_iff [DecidableEq I] {V : Over S} (a : V ⟶ U) :
    ActsBy e hg 1 a ↔ a ≫ g ∈ (torusCentralizer i).carrier V := by
  rw [mem_torusCentralizer]
  constructor
  · intro h V' c t
    rw [comp_eq_unitsPoint i e V' t]
    have h' := (conjUnits_eq_iff e hg (c ≫ a) _ _).1
      ((h V' c (pointsEquiv I V' (t ≫ e.hom.hom.hom))).trans (powUnits_one _))
    rw [Category.assoc] at h'
    exact mul_inv_eq_iff_eq_mul.1 h'
  · intro h V' c x
    rw [powUnits_one, conjUnits_eq_iff, Category.assoc]
    exact mul_inv_eq_of_eq_mul (h V' c ((pointsEquiv I V').symm x ≫ e.inv.hom.hom)).eq

/-- It suffices to test the action on affine test schemes. -/
theorem actsBy_of_forall_affine (m : Matrix I I ℤ) {V : Over S} (a : V ⟶ U)
    (h : ∀ (A : CommRingCat.{u}) (s : Spec A ⟶ S) (b : Over.mk s ⟶ V)
      (x : I → (Γ(Spec A, ⊤))ˣ), conjUnits e hg (b ≫ a) x = powUnits m x) :
    ActsBy e hg m a := by
  intro V' c x
  apply (pointsEquiv I V').symm.injective
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext V'.left.affineOpenCover.openCover _ _ fun j => ?_
  let d : Over.mk (V'.left.affineOpenCover.f j ≫ V'.hom) ⟶ V' :=
    Over.homMk (V'.left.affineOpenCover.f j)
  have key : d ≫ (pointsEquiv I V').symm (conjUnits e hg (c ≫ a) x) =
      d ≫ (pointsEquiv I V').symm (powUnits m x) := by
    rw [comp_pointsEquiv_symm, comp_pointsEquiv_symm, ← conjUnits_naturality, ← Category.assoc,
      h _ _ (d ≫ c)]
    congr 1
    exact powUnits_map d.left.appTop.hom m x
  exact congrArg (fun f => f.left) key

/-! ### Affine charts -/

/-- Global units of `Spec A` are units of `A`. -/
def specUnits (A : CommRingCat.{u}) : (Γ(Spec A, ⊤))ˣ ≃* Aˣ :=
  Units.mapEquiv (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv.toMulEquiv

theorem specUnits_naturality {A B : CommRingCat.{u}} (f : A ⟶ B) (x : (Γ(Spec A, ⊤))ˣ) :
    specUnits B (Units.map (Spec.map f).appTop.hom.toMonoidHom x) =
      Units.map f.hom.toMonoidHom (specUnits A x) := by
  apply Units.ext
  change ((Spec.map f).appTop ≫ (Scheme.ΓSpecIso B).hom) (x : Γ(Spec A, ⊤)) =
    ((Scheme.ΓSpecIso A).hom ≫ f) (x : Γ(Spec A, ⊤))
  rw [Scheme.ΓSpecIso_naturality]

variable {R : CommRingCat.{u}} {s : Spec R ⟶ S}

/-- The point over `Spec A` obtained from a point `ρ` over `Spec R` and a ring map
`α : R ⟶ A`. -/
def chartPoint (ρ : Over.mk s ⟶ U) {A : CommRingCat.{u}} (α : R ⟶ A) :
    Over.mk (Spec.map α ≫ s) ⟶ U :=
  (Over.homMk (Spec.map α) : Over.mk (Spec.map α ≫ s) ⟶ Over.mk s) ≫ ρ

/-- The comparison map between test schemes `Spec B ⟶ Spec A` over `S`. -/
abbrev chartMap {A B : CommRingCat.{u}} (α : R ⟶ A) (f : A ⟶ B) :
    Over.mk (Spec.map (α ≫ f) ≫ s) ⟶ Over.mk (Spec.map α ≫ s) :=
  Over.homMk (Spec.map f) (by simp [Spec.map_comp])

theorem chartMap_comp_chartPoint (ρ : Over.mk s ⟶ U) {A B : CommRingCat.{u}} (α : R ⟶ A)
    (f : A ⟶ B) : chartMap (s := s) α f ≫ chartPoint ρ α = chartPoint ρ (α ≫ f) := by
  apply Over.OverMorphism.ext
  simp [chartPoint, Spec.map_comp]

omit [Fintype I] in
/-- Conjugation by `g` in unit coordinates over the rings under `R`, through a chart
`ρ : Spec R ⟶ U`. -/
def chartFamily (ρ : Over.mk s ⟶ U) : UnitsNatEnd R I where
  app {A} α x := fun j => specUnits A (conjUnits e hg (chartPoint ρ α)
    (fun l => (specUnits A).symm (x l)) j)
  app_mul {A} α x y := by
    funext j
    have hxy : (fun l => (specUnits A).symm ((x * y) l)) =
        (fun l => (specUnits A).symm (x l)) * (fun l => (specUnits A).symm (y l)) := by
      funext l
      simp
    simp only [Pi.mul_apply]
    rw [show (fun l => (specUnits A).symm (x l * y l)) =
        (fun l => (specUnits A).symm (x l)) * (fun l => (specUnits A).symm (y l)) from hxy,
      conjUnits_mul, Pi.mul_apply, map_mul]
  naturality {A B} α f x := by
    funext j
    have hx : (fun l => (specUnits B).symm (Units.map f.hom.toMonoidHom (x l))) =
        unitsRestrict I (chartMap (s := s) α f) (fun l => (specUnits A).symm (x l)) := by
      funext l
      apply (specUnits B).injective
      rw [MulEquiv.apply_symm_apply]
      change _ = specUnits B (Units.map (Spec.map f).appTop.hom.toMonoidHom
        ((specUnits A).symm (x l)))
      rw [specUnits_naturality, MulEquiv.apply_symm_apply]
    change specUnits B (conjUnits e hg (chartPoint ρ (α ≫ f))
      (fun l => (specUnits B).symm (Units.map f.hom.toMonoidHom (x l))) j) = _
    rw [hx, ← chartMap_comp_chartPoint, conjUnits_naturality]
    change specUnits B (Units.map (Spec.map f).appTop.hom.toMonoidHom _) = _
    rw [specUnits_naturality]

theorem actsBy_chartPoint_iff (ρ : Over.mk s ⟶ U) {B : CommRingCat.{u}} (β : R ⟶ B)
    [DecidableEq I] (m : Matrix I I ℤ) :
    ActsBy e hg m (chartPoint ρ β) ↔
      ∀ j, β (((chartFamily e hg ρ).coeffs j).coeff (m j)) = 1 := by
  rw [← UnitsNatEnd.forall_app_eq_powUnits_iff]
  constructor
  · intro h A f x
    have h' := h _ (chartMap (s := s) β f) (fun l => (specUnits A).symm (x l))
    rw [chartMap_comp_chartPoint] at h'
    funext j
    change specUnits A (conjUnits e hg (chartPoint ρ (β ≫ f)) _ j) = _
    rw [h']
    simp [powUnits, map_prod, map_zpow]
  · intro h
    apply actsBy_of_forall_affine
    intro A s' b x
    let f : B ⟶ A := Spec.preimage b.left
    have hb : b.left = Spec.map f := (Spec.map_preimage b.left).symm
    rw [conjUnits_congr e hg (b ≫ chartPoint ρ β) (chartPoint ρ (β ≫ f))
      (by simp [chartPoint, hb, Spec.map_comp])]
    have hj := congrFun (h A f (fun l => specUnits A (x l)))
    funext j
    apply (specUnits A).injective
    have hj' := hj j
    simp only [chartFamily, MulEquiv.symm_apply_apply] at hj'
    rw [hj']
    simp [powUnits, map_prod, map_zpow]

theorem actsBy_chart_iff (ρ : Over.mk s ⟶ U) [DecidableEq I] (m : Matrix I I ℤ) :
    ActsBy e hg m ρ ↔ ∀ j, ((chartFamily e hg ρ).coeffs j).coeff (m j) = 1 := by
  rw [actsBy_congr e hg m ρ (chartPoint ρ (𝟙 R)) (by simp [chartPoint]),
    actsBy_chartPoint_iff]
  simp

/-! ### Points -/

/-- A morphism of schemes into `U` as a morphism over `S`. -/
abbrev overHom {X : Scheme.{u}} (y : X ⟶ U.left) : Over.mk (y ≫ U.hom) ⟶ U :=
  Over.homMk y

/-- Conjugation by `g` acts by `m` on the torus over the residue field at `x`. -/
def ActsAtPoint (m : Matrix I I ℤ) (x : U.left) : Prop :=
  ActsBy e hg m (overHom (U := U) (U.left.fromSpecResidueField x))

theorem actsBy_overHom_iff [DecidableEq I] {K : Type u} [Field K]
    (y : Spec (CommRingCat.of K) ⟶ U.left) (m : Matrix I I ℤ) :
    ActsBy e hg m (overHom (U := U) y) ↔ ActsAtPoint e hg m (y (IsLocalRing.closedPoint K)) := by
  let ψ := Scheme.descResidueField (Scheme.stalkClosedPointTo y)
  have hy : Spec.map ψ ≫ U.left.fromSpecResidueField (y (IsLocalRing.closedPoint K)) = y :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K U.left y
  let ρ := overHom (U := U) (U.left.fromSpecResidueField (y (IsLocalRing.closedPoint K)))
  rw [actsBy_congr e hg m (overHom (U := U) y) (chartPoint ρ ψ) (by simp [chartPoint, ρ, hy]),
    actsBy_chartPoint_iff, ActsAtPoint, actsBy_chart_iff]
  refine forall_congr' fun j => ⟨fun h => ψ.hom.injective (by rw [h, map_one]), fun h => ?_⟩
  rw [h, map_one]

theorem algebraMap_residueField_eq_one_iff {A : Type u} [CommRing A] {d : A}
    (hd : IsIdempotentElem d) (P : Ideal A) [P.IsPrime] :
    algebraMap A P.ResidueField d = 1 ↔ d ∉ P := by
  rw [← Ideal.algebraMap_residueField_eq_zero]
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 (hd.map (algebraMap A P.ResidueField)) with h | h
  · simp [h]
  · simp [h]

theorem mem_iff_one_sub_notMem {A : Type u} [CommRing A] {d : A} (hd : IsIdempotentElem d)
    (P : Ideal A) [hP : P.IsPrime] : d ∈ P ↔ 1 - d ∉ P := by
  constructor
  · intro h h'
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one]
    simpa using P.add_mem h h'
  · intro h
    have hm : d * (1 - d) ∈ P := by
      rw [mul_sub, mul_one, hd.eq, sub_self]
      exact P.zero_mem
    exact (hP.mem_or_mem hm).resolve_right h

theorem actsAtPoint_chart_iff [DecidableEq I] (ρ : Over.mk s ⟶ U) (m : Matrix I I ℤ)
    (p : PrimeSpectrum R) :
    ActsAtPoint e hg m (ρ.left p) ↔
      ∀ j, ((chartFamily e hg ρ).coeffs j).coeff (m j) ∉ p.asIdeal := by
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
  rw [← hpt, ← actsBy_overHom_iff,
    actsBy_congr e hg m (overHom (U := U) (Spec.map β ≫ ρ.left)) (chartPoint ρ β) rfl,
    actsBy_chartPoint_iff]
  exact forall_congr' fun j => algebraMap_residueField_eq_one_iff
    ((chartFamily e hg ρ).isIdempotentElem_coeff j (m j)) p.asIdeal

/-- The locus where conjugation by `g` acts by `m` is open and closed. -/
theorem isLocallyConstant_actsAtPoint [DecidableEq I] (m : Matrix I I ℤ) :
    IsLocallyConstant (ActsAtPoint e hg m) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  obtain ⟨k, p₀, hp₀⟩ : ∃ k p₀, U.left.affineOpenCover.f k p₀ = x :=
    ⟨_, U.left.affineOpenCover.covers x⟩
  subst hp₀
  let b := U.left.affineOpenCover.f k
  let ρ := overHom (U := U) b
  let c : I → U.left.affineOpenCover.X k :=
    fun j => ((chartFamily e hg ρ).coeffs j).coeff (m j)
  let P : PrimeSpectrum (U.left.affineOpenCover.X k) → Prop :=
    fun p => ∀ j, c j ∉ p.asIdeal
  have hP : ∀ p, ActsAtPoint e hg m (b p) ↔ P p := fun p => actsAtPoint_chart_iff e hg ρ m p
  have hopen : IsOpen {p | P p ↔ P p₀} := by
    by_cases h0 : P p₀
    · have hset : {p | P p ↔ P p₀} = ⋂ j, (PrimeSpectrum.basicOpen (c j) : Set _) := by
        ext p
        simp [P, h0]
      rw [hset]
      exact isOpen_iInter_of_finite fun j => (PrimeSpectrum.basicOpen (c j)).isOpen
    · have hset : {p | P p ↔ P p₀} = ⋃ j, (PrimeSpectrum.basicOpen (1 - c j) : Set _) := by
        ext p
        simp only [Set.mem_ofPred_eq, h0, iff_false, P, not_forall, not_not, Set.mem_iUnion,
          SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
        exact exists_congr fun j => mem_iff_one_sub_notMem
          ((chartFamily e hg ρ).isIdempotentElem_coeff j (m j)) p.asIdeal
      rw [hset]
      exact isOpen_iUnion fun j => (PrimeSpectrum.basicOpen (1 - c j)).isOpen
  refine ⟨b '' {p | P p ↔ P p₀}, b.isOpenEmbedding.isOpenMap _ hopen, ⟨p₀, Iff.rfl, rfl⟩, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  exact propext ((hP p).trans (hp.trans (hP p₀).symm))

theorem actsAtPoint_of_preconnected [PreconnectedSpace U.left] [DecidableEq I]
    (m : Matrix I I ℤ) {x₀ : U.left} (h₀ : ActsAtPoint e hg m x₀) (x : U.left) :
    ActsAtPoint e hg m x := by
  rw [(isLocallyConstant_actsAtPoint e hg m).apply_eq_of_preconnectedSpace x x₀]
  exact h₀

/-- If conjugation by `g` acts by `m` at every point, it acts by `m` over every test scheme. -/
theorem actsBy_of_forall_actsAtPoint [DecidableEq I] (m : Matrix I I ℤ)
    (h : ∀ x, ActsAtPoint e hg m x) : ActsBy e hg m (𝟙 U) := by
  apply actsBy_of_forall_affine
  intro A s' b x
  have hd : ∀ j, ((chartFamily e hg b).coeffs j).coeff (m j) = 1 := by
    intro j
    have hu : IsUnit (((chartFamily e hg b).coeffs j).coeff (m j)) := by
      by_contra hd
      obtain ⟨P, hP, hdP⟩ := exists_max_ideal_of_mem_nonunits hd
      exact (actsAtPoint_chart_iff e hg b m ⟨P, hP.isPrime⟩).1 (h _) j hdP
    have hid := (chartFamily e hg b).isIdempotentElem_coeff j (m j)
    exact hu.mul_left_cancel (by rw [hid.eq, mul_one])
  have hb := (actsBy_chart_iff e hg b m).2 hd _ (𝟙 _) x
  rw [Category.id_comp] at hb
  rw [Category.comp_id]
  exact hb

/-- Over a residue field the conjugation action is a monomial map. -/
theorem exists_actsAtPoint [DecidableEq I] (x : U.left) : ∃ m, ActsAtPoint e hg m x := by
  obtain ⟨m, hm⟩ := (chartFamily e hg (overHom (U := U) (U.left.fromSpecResidueField x))).exists_forall_coeff_eq_one (𝟙 _)
  exact ⟨m, (actsBy_chart_iff e hg _ m).2 hm⟩

/-- **Rigidity.** Over a connected test scheme, conjugation by a torus-normalizing point acts
on the torus by the monomial map of one exponent matrix. -/
theorem exists_actsBy_of_connected [ConnectedSpace U.left] [DecidableEq I] :
    ∃ m : Matrix I I ℤ, ActsBy e hg m (𝟙 U) := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty U.left)
  obtain ⟨m, hm⟩ := exists_actsAtPoint e hg x₀
  exact ⟨m, actsBy_of_forall_actsAtPoint e hg m (actsAtPoint_of_preconnected e hg m hm)⟩

include e hg in
/-- Over a connected test scheme, a torus-normalizing point centralizes the torus as soon as
it does so over the residue field of one point. -/
theorem mem_torusCentralizer_of_connected [PreconnectedSpace U.left] {x₀ : U.left}
    (h₀ : overHom (U := U) (U.left.fromSpecResidueField x₀) ≫ g ∈
      (torusCentralizer i).carrier _) :
    g ∈ (torusCentralizer i).carrier U := by
  classical
  have h1 : ActsAtPoint e hg 1 x₀ := (actsBy_one_iff e hg _).2 h₀
  have h2 := (actsBy_one_iff e hg (𝟙 U)).1
    (actsBy_of_forall_actsAtPoint e hg 1 (actsAtPoint_of_preconnected e hg 1 h1))
  rwa [Category.id_comp] at h2

omit [Fintype I] in
/-- Conjugating by `g⁻¹` undoes conjugating by `g`. -/
theorem conjUnits_inv_conjUnits (hg' : g⁻¹ ∈ (torusNormalizer i).carrier U) {V : Over S}
    (a : V ⟶ U) (x : I → (Γ(V.left, ⊤))ˣ) : conjUnits e hg' a (conjUnits e hg a x) = x := by
  rw [conjUnits_eq_iff, ← conjUnits_spec e hg a x, GrpObj.comp_inv]
  group

/-- Over a nonempty test scheme, the exponent matrices of `g` and `g⁻¹` are inverse. -/
theorem mul_eq_one_of_actsBy [DecidableEq I] [Nonempty U.left]
    (hg' : g⁻¹ ∈ (torusNormalizer i).carrier U) {m m' : Matrix I I ℤ}
    (hm : ActsBy e hg m (𝟙 U)) (hm' : ActsBy e hg' m' (𝟙 U)) : m' * m = 1 := by
  obtain ⟨x₀⟩ := ‹Nonempty U.left›
  let ρ := overHom (U := U) (U.left.fromSpecResidueField x₀)
  let c := chartPoint ρ (laurentAlgebraMap (U.left.residueField x₀) I)
  let X : I → (Γ(Spec (laurentRing (U.left.residueField x₀) I), ⊤))ˣ :=
    fun j => (specUnits _).symm (UnitsNatEnd.universalUnits _ I j)
  have h1 := hm _ c X
  have h2 := hm' _ c (powUnits m X)
  rw [Category.comp_id] at h1 h2
  have h2' := conjUnits_inv_conjUnits e hg hg' c X
  rw [h1, h2, powUnits_powUnits] at h2'
  have hcomm : ∀ (M : Matrix I I ℤ) (y : I → (Γ(Spec (laurentRing (U.left.residueField x₀) I), ⊤))ˣ),
      (fun j => specUnits _ (powUnits M y j)) = powUnits M (fun j => specUnits _ (y j)) := by
    intro M y
    funext j
    simp [powUnits, map_prod, map_zpow]
  have h4 : powUnits (m' * m) (UnitsNatEnd.universalUnits (U.left.residueField x₀) I) =
      UnitsNatEnd.universalUnits (U.left.residueField x₀) I := by
    have h := congrArg (fun y => fun j => specUnits _ (y j)) h2'
    simp only [hcomm, X, MulEquiv.apply_symm_apply] at h
    exact h
  rw [UnitsNatEnd.powUnits_universalUnits] at h4
  ext j l
  have h5 := congrArg (fun y => ((y j : laurentRing (U.left.residueField x₀) I) :
    AddMonoidAlgebra (U.left.residueField x₀) (I → ℤ)).coeff ((m' * m) j)) h4
  simp only [exponentUnit_val, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at h5
  have h6 : (m' * m) j = Pi.single j 1 := by
    by_contra hne
    rw [Finsupp.single_apply, ite_eq_right (Ne.symm hne)] at h5
    exact one_ne_zero h5
  rw [h6, Matrix.one_apply, Pi.single_apply]
  by_cases hjl : j = l
  · subst hjl
    simp
  · simp [hjl, Ne.symm hjl]

end Points

/-! ### The automorphism of the torus -/

section Aut

variable {S : Scheme.{u}} {I : Type u} [Fintype I] [DecidableEq I]

/-- The monomial map of an invertible exponent matrix on the points of the split torus. -/
def splitTorusPowEquiv {m m' : Matrix I I ℤ} (h₁ : m' * m = 1) (h₂ : m * m' = 1) (V : Over S) :
    (V ⟶ (splitTorus S I).X) ≃* (V ⟶ (splitTorus S I).X) :=
  (pointsEquiv I V).trans ((powUnitsEquiv (Γ(V.left, ⊤)) h₁ h₂).trans (pointsEquiv I V).symm)

theorem splitTorusPowEquiv_apply {m m' : Matrix I I ℤ} (h₁ : m' * m = 1) (h₂ : m * m' = 1)
    (V : Over S) (x : V ⟶ (splitTorus S I).X) :
    splitTorusPowEquiv h₁ h₂ V x = (pointsEquiv I V).symm (powUnits m (pointsEquiv I V x)) :=
  rfl

theorem splitTorusPowEquiv_naturality {m m' : Matrix I I ℤ} (h₁ : m' * m = 1) (h₂ : m * m' = 1)
    {V V' : Over S} (a : V' ⟶ V) (x : V ⟶ (splitTorus S I).X) :
    splitTorusPowEquiv h₁ h₂ V' (a ≫ x) = a ≫ splitTorusPowEquiv h₁ h₂ V x := by
  rw [splitTorusPowEquiv_apply, splitTorusPowEquiv_apply, pointsEquiv_naturality,
    comp_pointsEquiv_symm]
  congr 1
  exact powUnits_map _ m _

/-- The automorphism of the split torus given by an invertible exponent matrix. -/
def splitTorusPowIso {m m' : Matrix I I ℤ} (h₁ : m' * m = 1) (h₂ : m * m' = 1) :
    splitTorus S I ≅ splitTorus S I :=
  isoOfPoints (splitTorusPowEquiv h₁ h₂) (splitTorusPowEquiv_naturality h₁ h₂)

theorem comp_splitTorusPowIso_hom {m m' : Matrix I I ℤ} (h₁ : m' * m = 1) (h₂ : m * m' = 1)
    (V : Over S) (x : V ⟶ (splitTorus S I).X) :
    x ≫ (splitTorusPowIso (S := S) h₁ h₂).hom.hom.hom =
      (pointsEquiv I V).symm (powUnits m (pointsEquiv I V x)) :=
  comp_isoOfPoints_hom _ (splitTorusPowEquiv_naturality h₁ h₂) V x

end Aut

section Normalizing

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S} {i : T.toGrp ⟶ G}

/-- **Rigidity of torus normalizers.** Over a connected test scheme `U`, conjugation by a point
of the torus normalizer acts on the torus by one automorphism `σ` of `T` over the base. -/
theorem exists_isNormalizingAut_of_connected [Mono i.hom.hom.left] (hT : IsSplitTorus T.toGrp)
    {U : Over S} [ConnectedSpace U.left] {g : U ⟶ G.X} (hg : g ∈ (torusNormalizer i).carrier U) :
    ∃ σ : T ≅ T, ∀ (V : Over S) (a : V ⟶ U) (t : V ⟶ T.X),
      (a ≫ g) * (t ≫ i.hom.hom) * (a ≫ g)⁻¹ =
        (t ≫ (CommGroupScheme.groupHom σ.hom).hom.hom) ≫ i.hom.hom := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let _ : Fintype I := Fintype.ofFinite I
  have hg' : g⁻¹ ∈ (torusNormalizer i).carrier U := ((torusNormalizer i).carrier U).inv_mem hg
  obtain ⟨m, hm⟩ := exists_actsBy_of_connected e hg
  obtain ⟨m', hm'⟩ := exists_actsBy_of_connected e hg'
  have h₁ : m' * m = 1 := mul_eq_one_of_actsBy e hg hg' hm hm'
  have h₂ : m * m' = 1 := mul_eq_one_comm.1 h₁
  let τ : T.toGrp ≅ T.toGrp := e ≪≫ splitTorusPowIso h₁ h₂ ≪≫ e.symm
  refine ⟨{ hom := Additive.ofMul τ.hom
            inv := Additive.ofMul τ.inv
            hom_inv_id := congrArg Additive.ofMul τ.hom_inv_id
            inv_hom_id := congrArg Additive.ofMul τ.inv_hom_id }, ?_⟩
  intro V a t
  change _ = (t ≫ τ.hom.hom.hom) ≫ i.hom.hom
  have hc : conjUnits e hg a (pointsEquiv I V (t ≫ e.hom.hom.hom)) =
      powUnits m (pointsEquiv I V (t ≫ e.hom.hom.hom)) := by
    simpa using hm V a (pointsEquiv I V (t ≫ e.hom.hom.hom))
  rw [comp_eq_unitsPoint i e V t, conjUnits_spec e hg a, hc, unitsPoint,
    ← comp_splitTorusPowIso_hom h₁ h₂]
  simp only [τ, Iso.trans_hom, Iso.symm_hom, Grp.comp_hom_hom, Category.assoc]

end Normalizing

/-! ### Injectivity over a field -/

section Field

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)

/-- A normalizing point over `k` whose restriction to a nonempty test scheme centralizes the
torus centralizes the torus. -/
theorem mem_centralizerPoints_of_constantPoint [Mono i.hom.hom.left]
    (hT : IsSplitTorus T.toGrp) {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hn : n ∈ normalizerPoints i) (U : Over (Spec (CommRingCat.of k))) [Nonempty U.left]
    (h : G.constantPoint n U ∈ (torusCentralizer i).carrier U) : n ∈ centralizerPoints i := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let _ : Fintype I := Fintype.ofFinite I
  have hnN : n ∈ (torusNormalizer i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
    normalizerPoints_le_torusNormalizer i hn
  obtain ⟨x₀⟩ := ‹Nonempty U.left›
  let γ : CommRingCat.of k ⟶ U.left.residueField x₀ :=
    Spec.preimage (U.left.fromSpecResidueField x₀ ≫ U.hom)
  have hγ : Spec.map γ = U.left.fromSpecResidueField x₀ ≫ U.hom :=
    Spec.map_preimage _
  let b₀ : Over.mk (Spec.map γ ≫ 𝟙 (Spec (CommRingCat.of k))) ⟶ U :=
    Over.homMk (U.left.fromSpecResidueField x₀) (by simp [hγ])
  have hb₀ : b₀ ≫ (Over.homMk U.hom (by simp) : U ⟶ Over.mk (𝟙 _)) =
      chartPoint (𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of k))))) γ := by
    apply Over.OverMorphism.ext
    simp [b₀, chartPoint, hγ]
  have h1 : ActsBy e hnN 1 (chartPoint (𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of k))))) γ) := by
    rw [actsBy_one_iff, ← hb₀, Category.assoc]
    exact (torusCentralizer i).comp_mem b₀ h
  rw [actsBy_chartPoint_iff] at h1
  have h2 : ActsBy e hnN 1 (𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of k))))) := by
    rw [actsBy_chart_iff]
    intro j
    apply γ.hom.injective
    rw [h1 j, map_one]
  rw [actsBy_one_iff, Category.id_comp, torusCentralizer_carrier_base] at h2
  exact h2

end Field

end TorusConjugation

/-- Restriction `N(k)/Z(k) → N(U)/Z(U)` is injective for every test scheme `U` with a point. -/
theorem relativeWeylGroupRestrict_injective {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {G : GroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (hT : IsSplitTorus T.toGrp)
    (U : Over (Spec (CommRingCat.of k))) [Nonempty U.left] :
    Function.Injective (relativeWeylGroupRestrict i U) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  induction w using QuotientGroup.induction_on with
  | H n =>
    rw [relativeWeylGroupRestrict_mk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hw
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact TorusConjugation.mem_centralizerPoints_of_constantPoint i hT n.2 U hw

end Langlands.GroupScheme
