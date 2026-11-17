import Langlands.GroupScheme.Torus.DiagonalizableRigidityStatement
import Langlands.GroupScheme.Torus.DiagonalizableCharacterProof
import Mathlib.AlgebraicGeometry.AffineSpace

/-! # Rigidity of families of homomorphisms between diagonalizable groups: proof

A family of homomorphisms `D(Λ) → 𝔾_m` parametrized by a scheme `X` is recorded on all
`Y`-points `y` of `X` as multiplicative maps `Hom(Λ, Γ(Y)ˣ) → Γ(Y)ˣ` (`CharFamily`). Over an
affine chart `Spec A → X` it is a `NaturalUnits A Λ` of the Library, whose universal value in
`A[Λ]` is grouplike, so its coefficients are orthogonal idempotents with sum `1`. The locus of
points where the family is evaluation at `m ∈ Λ` is open and closed, so over a connected `X`
the family is evaluation at one `m`. Applying this to every coordinate of `D(Λ')` proves the
rigidity theorem.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace DiagonalizableRigidity

open DiagonalizableCharacter

/-- Global sections of a scheme are determined by their pullbacks along an open cover. -/
theorem eq_of_cover {Y : Scheme.{u}} (𝒰 : Y.OpenCover) {a b : Γ(Y, ⊤)}
    (h : ∀ j, (𝒰.f j).appTop a = (𝒰.f j).appTop b) : a = b := by
  have key : (AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}).symm (fun _ => a) =
      (AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}).symm (fun _ => b) := by
    refine Scheme.Cover.hom_ext 𝒰 _ _ fun j => ?_
    apply (AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}).injective
    funext i
    rw [AffineSpace.toSpecMvPolyIntEquiv_comp, AffineSpace.toSpecMvPolyIntEquiv_comp,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact h j
  have := congrFun (congrArg (AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}) key) PUnit.unit
  rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this

/-- Restriction of a character with values in global units along a morphism of schemes. -/
abbrev resChar {Λ : Type u} [AddCommGroup Λ] {Y Y' : Scheme.{u}} (t : Y' ⟶ Y)
    (χ : Multiplicative Λ →* Γ(Y, ⊤)ˣ) : Multiplicative Λ →* Γ(Y', ⊤)ˣ :=
  (Units.map t.appTop.hom.toMonoidHom).comp χ

/-- The character of a restricted point of `D(Λ)` is the restricted character. -/
theorem characterPointsEquiv_comp {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]
    {U U' : Over (Spec R)} (a : U' ⟶ U) (x : U ⟶ (Diagonalizable.groupScheme R Λ).X) :
    Diagonalizable.characterPointsEquiv R Λ U' (a ≫ x) =
      resChar a.left (Diagonalizable.characterPointsEquiv R Λ U x) :=
  MonoidHom.ext fun l => Diagonalizable.characterPointsEquiv_naturality R Λ a x l.toAdd

/-- A family of homomorphisms `D(Λ) → 𝔾_m` parametrized by a scheme `X`, on points: for every
`Y`-point `y` of `X`, a homomorphism from the characters `Λ → Γ(Y)ˣ` (the `Y`-points of `D(Λ)`)
to the units `Γ(Y)ˣ` (the `Y`-points of `𝔾_m`), natural in `Y`. -/
structure CharFamily (X : Scheme.{u}) (Λ : Type u) [AddCommGroup Λ] where
  /-- The homomorphism at a `Y`-point of `X`. -/
  app : ∀ {Y : Scheme.{u}}, (Y ⟶ X) → (Multiplicative Λ →* Γ(Y, ⊤)ˣ) →* Γ(Y, ⊤)ˣ
  /-- Naturality in the test scheme. -/
  naturality : ∀ {Y Y' : Scheme.{u}} (t : Y' ⟶ Y) (y : Y ⟶ X)
    (χ : Multiplicative Λ →* Γ(Y, ⊤)ˣ),
    app (t ≫ y) (resChar t χ) = Units.map t.appTop.hom.toMonoidHom (app y χ)

namespace CharFamily

variable {X : Scheme.{u}} {Λ : Type u} [AddCommGroup Λ] (c : CharFamily X Λ)

/-- The family over a chart `ρ : Spec A ⟶ X`, as a natural family of units on the points of
`D(Λ)` over `Spec A`. -/
def chartUnits {A : CommRingCat.{u}} (ρ : Spec A ⟶ X) : NaturalUnits A Λ where
  app U := (c.app (U.hom ≫ ρ)).comp (Diagonalizable.characterPointsEquiv A Λ U).toMonoidHom
  naturality {U U'} a x := by
    change c.app (U'.hom ≫ ρ) (Diagonalizable.characterPointsEquiv A Λ U' (a ≫ x)) =
      Units.map a.left.appTop.hom.toMonoidHom
        (c.app (U.hom ≫ ρ) (Diagonalizable.characterPointsEquiv A Λ U x))
    rw [characterPointsEquiv_comp, ← Over.w a, Category.assoc, c.naturality]

theorem chartUnits_app_symm {A : CommRingCat.{u}} (ρ : Spec A ⟶ X) (U : Over (Spec A))
    (χ : Multiplicative Λ →* Γ(U.left, ⊤)ˣ) :
    (c.chartUnits ρ).app U ((Diagonalizable.characterPointsEquiv A Λ U).symm χ) =
      c.app (U.hom ≫ ρ) χ := by
  change c.app (U.hom ≫ ρ) (Diagonalizable.characterPointsEquiv A Λ U
    ((Diagonalizable.characterPointsEquiv A Λ U).symm χ)) = _
  rw [MulEquiv.apply_symm_apply]

/-- `c` is evaluation at `m` over `y`: at every point over `y`. -/
def ActsBy (m : Λ) {Y : Scheme.{u}} (y : Y ⟶ X) : Prop :=
  ∀ (Y' : Scheme.{u}) (t : Y' ⟶ Y) (χ : Multiplicative Λ →* Γ(Y', ⊤)ˣ),
    c.app (t ≫ y) χ = χ (.ofAdd m)

/-- Over a chart, `c` is evaluation at `m` exactly when the universal value is `single m 1`. -/
theorem actsBy_iff_value {A : CommRingCat.{u}} (ρ : Spec A ⟶ X) (m : Λ) :
    c.ActsBy m ρ ↔ (c.chartUnits ρ).value = AddMonoidAlgebra.single m 1 := by
  rw [← NaturalUnits.app_eq_iff]
  constructor
  · intro h U x
    exact h U.left U.hom _
  · intro h Y' t χ
    have := h (Over.mk t) ((Diagonalizable.characterPointsEquiv A Λ (Over.mk t)).symm χ)
    rw [chartUnits_app_symm, MulEquiv.apply_symm_apply] at this
    exact this

/-- The structure map `A → Γ(Y)` of a morphism `t : Y ⟶ Spec A`. -/
abbrev sectionMap {A : CommRingCat.{u}} {Y : Scheme.{u}} (t : Y ⟶ Spec A) : A →+* Γ(Y, ⊤) :=
  ((Scheme.ΓSpecIso A).inv ≫ t.appTop).hom

/-- **Expansion.** Through a chart `ρ`, the family is `χ ↦ ∑ₙ vₙ χ(n)` for the universal value
`v = ∑ₙ vₙ n`. -/
theorem app_eq_sum {A : CommRingCat.{u}} (ρ : Spec A ⟶ X) {Y : Scheme.{u}} (t : Y ⟶ Spec A)
    (χ : Multiplicative Λ →* Γ(Y, ⊤)ˣ) :
    (c.app (t ≫ ρ) χ : Γ(Y, ⊤)) = (c.chartUnits ρ).value.coeff.sum
      fun a b => sectionMap t b * (χ (.ofAdd a) : Γ(Y, ⊤)) := by
  have h := (c.chartUnits ρ).app_eq (Over.mk t)
    ((Diagonalizable.characterPointsEquiv A Λ (Over.mk t)).symm χ)
  rw [chartUnits_app_symm, MulEquiv.apply_symm_apply] at h
  refine h.trans ?_
  exact AddMonoidAlgebra.lift_apply' (A := ((algΓ A).obj (Over.mk t)).unop) _ _

/-- If the coefficient `vₘ` becomes `1` on `Y`, the family is evaluation at `m` over `Y`. -/
theorem actsBy_of_sectionMap {A : CommRingCat.{u}} (ρ : Spec A ⟶ X) {Y : Scheme.{u}}
    (t : Y ⟶ Spec A) (m : Λ) (h : sectionMap t ((c.chartUnits ρ).value.coeff m) = 1) :
    c.ActsBy m (t ≫ ρ) := by
  have hv := (c.chartUnits ρ).isGrouplike_value
  have h0 : ∀ n, n ≠ m → sectionMap t ((c.chartUnits ρ).value.coeff n) = 0 := by
    intro n hn
    have e : (c.chartUnits ρ).value.coeff n * (c.chartUnits ρ).value.coeff m = 0 :=
      hv.coeff_mul_coeff_of_ne hn.symm
    calc sectionMap t ((c.chartUnits ρ).value.coeff n)
        = sectionMap t ((c.chartUnits ρ).value.coeff n) *
            sectionMap t ((c.chartUnits ρ).value.coeff m) := by rw [h, mul_one]
      _ = 0 := by rw [← map_mul, e, map_zero]
  intro Y' t' χ
  apply Units.ext
  have hs : ∀ b, sectionMap (t' ≫ t) b = t'.appTop (sectionMap t b) := fun b => rfl
  rw [← Category.assoc, app_eq_sum, Finsupp.sum_eq_single m]
  · rw [hs, h, map_one, one_mul]
  · intro b _ hb
    rw [hs, h0 b hb, map_zero, zero_mul]
  · intro _
    rw [map_zero, zero_mul]

/-- At every prime of a chart some coefficient of the universal value is a unit. -/
theorem exists_coeff_notMem {A : CommRingCat.{u}} (ρ : Spec A ⟶ X) (p : PrimeSpectrum A) :
    ∃ m, (c.chartUnits ρ).value.coeff m ∉ p.asIdeal := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  have hv := (c.chartUnits ρ).isGrouplike_value
  have hs : (∑ n ∈ (c.chartUnits ρ).value.coeff.support, (c.chartUnits ρ).value.coeff n) ∈
      p.asIdeal := Ideal.sum_mem _ fun n _ => hall n
  have h1 : (∑ n ∈ (c.chartUnits ρ).value.coeff.support, (c.chartUnits ρ).value.coeff n) = 1 :=
    hv.sum_coeff
  rw [h1] at hs
  exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hs)

/-! ### The locus of a character -/

/-- The points of `X` over whose residue field the family is evaluation at `m`. -/
def Locus (m : Λ) : Set X := {x | c.ActsBy m (X.fromSpecResidueField x)}

/-- In an open chart, the locus of `m` contains the points where `vₘ` is a unit. -/
theorem mem_locus_of_chart {A : CommRingCat.{u}} (ρ : Spec A ⟶ X) [IsOpenImmersion ρ]
    (p : PrimeSpectrum A) (m : Λ) (hp : (c.chartUnits ρ).value.coeff m ∉ p.asIdeal) :
    ρ p ∈ c.Locus m := by
  have hv := (c.chartUnits ρ).isGrouplike_value
  have hid : IsIdempotentElem ((c.chartUnits ρ).value.coeff m) := hv.isIdempotentElem_coeff m
  have H : Set.range (X.fromSpecResidueField (ρ p)) ⊆ Set.range ρ := by
    rw [Scheme.range_fromSpecResidueField]
    rintro _ rfl
    exact ⟨p, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t ≫ ρ = X.fromSpecResidueField (ρ p) :=
    ⟨IsOpenImmersion.lift ρ (X.fromSpecResidueField (ρ p)) H, IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨β, hβ⟩ : ∃ β, Spec.map β = t := ⟨Spec.preimage t, Spec.map_preimage t⟩
  subst hβ
  have hpt : Spec.map β (IsLocalRing.closedPoint (X.residueField (ρ p))) = p := by
    apply ρ.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ht, Scheme.fromSpecResidueField_apply]
  have hne : β.hom ((c.chartUnits ρ).value.coeff m) ≠ 0 := by
    intro h0
    apply hp
    rw [← hpt, Spec.map_apply]
    change β.hom ((c.chartUnits ρ).value.coeff m) ∈ IsLocalRing.maximalIdeal _
    rw [h0]
    exact Ideal.zero_mem _
  have h1 : β.hom ((c.chartUnits ρ).value.coeff m) = 1 :=
    ((IsIdempotentElem.iff_eq_zero_or_one).1 (hid.map β.hom)).resolve_left hne
  have := c.actsBy_of_sectionMap ρ (Spec.map β) m (by
    change ((Scheme.ΓSpecIso A).inv ≫ (Spec.map β).appTop).hom _ = 1
    rw [← Scheme.ΓSpecIso_inv_naturality, CommRingCat.hom_comp, RingHom.comp_apply, h1,
      map_one])
  rw [ht] at this
  exact this

/-- A point lies in the locus of at most one character. -/
theorem eq_of_mem_locus {x : X} {m n : Λ} (hm : x ∈ c.Locus m) (hn : x ∈ c.Locus n) :
    m = n := by
  have h1 := (c.actsBy_iff_value (X.fromSpecResidueField x) m).1 hm
  have h2 := (c.actsBy_iff_value (X.fromSpecResidueField x) n).1 hn
  exact AddMonoidAlgebra.single_left_injective (one_ne_zero (α := X.residueField x))
    (h1.symm.trans h2)

/-- Every point lies in some locus. -/
theorem exists_mem_locus (x : X) : ∃ m, x ∈ c.Locus m := by
  obtain ⟨p, hp⟩ := X.affineOpenCover.covers x
  obtain ⟨m, hm⟩ := c.exists_coeff_notMem (X.affineOpenCover.f (X.affineOpenCover.idx x)) p
  refine ⟨m, ?_⟩
  rw [← hp]
  exact c.mem_locus_of_chart _ p m hm

theorem isOpen_locus (m : Λ) : IsOpen (c.Locus m) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨p, hp⟩ := X.affineOpenCover.covers x
  obtain ⟨n, hn⟩ := c.exists_coeff_notMem (X.affineOpenCover.f (X.affineOpenCover.idx x)) p
  have hxn : x ∈ c.Locus n := hp ▸ c.mem_locus_of_chart _ p n hn
  obtain rfl := c.eq_of_mem_locus hxn hx
  let V : Set (PrimeSpectrum (X.affineOpenCover.X (X.affineOpenCover.idx x))) :=
    PrimeSpectrum.basicOpen ((c.chartUnits
      (X.affineOpenCover.f (X.affineOpenCover.idx x))).value.coeff n)
  refine ⟨X.affineOpenCover.f (X.affineOpenCover.idx x) '' V, ?_, ?_,
    ⟨p, (PrimeSpectrum.mem_basicOpen _ _).2 hn, hp⟩⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact c.mem_locus_of_chart _ q n ((PrimeSpectrum.mem_basicOpen _ _).1 hq)
  · exact (X.affineOpenCover.f (X.affineOpenCover.idx x)).isOpenEmbedding.isOpenMap _
      (PrimeSpectrum.basicOpen _).isOpen

theorem isClosed_locus (m : Λ) : IsClosed (c.Locus m) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨n, hn⟩ := c.exists_mem_locus x
  refine ⟨c.Locus n, fun y hy hym => ?_, c.isOpen_locus n, hn⟩
  obtain rfl := c.eq_of_mem_locus hy hym
  exact hx hn

/-- If the locus of `m` is everything, the family is evaluation at `m` over every open chart. -/
theorem actsBy_of_locus {m : Λ} (hm : ∀ x, x ∈ c.Locus m) {A : CommRingCat.{u}}
    (ρ : Spec A ⟶ X) [IsOpenImmersion ρ] : c.ActsBy m ρ := by
  have hv := (c.chartUnits ρ).isGrouplike_value
  have hid : IsIdempotentElem ((c.chartUnits ρ).value.coeff m) := hv.isIdempotentElem_coeff m
  have hu : IsUnit ((c.chartUnits ρ).value.coeff m) := by
    by_contra hd
    obtain ⟨P, hP, hdP⟩ := exists_max_ideal_of_mem_nonunits hd
    obtain ⟨n, hn⟩ := c.exists_coeff_notMem ρ ⟨P, hP.isPrime⟩
    obtain rfl := c.eq_of_mem_locus (c.mem_locus_of_chart ρ ⟨P, hP.isPrime⟩ n hn) (hm _)
    exact hn hdP
  have h1 : (c.chartUnits ρ).value.coeff m = 1 :=
    hu.mul_left_cancel (by rw [hid.eq, mul_one])
  have := c.actsBy_of_sectionMap ρ (𝟙 _) m (by rw [h1, map_one])
  rwa [Category.id_comp] at this

/-- If the locus of `m` is everything, the family is evaluation at `m` at every point. -/
theorem app_eq_of_locus {m : Λ} (hm : ∀ x, x ∈ c.Locus m) {Y : Scheme.{u}} (y : Y ⟶ X)
    (χ : Multiplicative Λ →* Γ(Y, ⊤)ˣ) : c.app y χ = χ (.ofAdd m) := by
  apply Units.ext
  refine eq_of_cover (X.affineOpenCover.openCover.pullback₁ y) fun j => ?_
  have h1 := c.naturality ((X.affineOpenCover.openCover.pullback₁ y).f j) y χ
  rw [← Scheme.Cover.pullbackHom_map] at h1
  have h2 := c.actsBy_of_locus hm (X.affineOpenCover.f j) _
    (X.affineOpenCover.openCover.pullbackHom y j)
    (resChar ((X.affineOpenCover.openCover.pullback₁ y).f j) χ)
  have h3 := h1.symm.trans h2
  exact congrArg Units.val h3

/-- **Rigidity for one character.** Over a connected scheme, a family of homomorphisms
`D(Λ) → 𝔾_m` is evaluation at one `m ∈ Λ`. -/
theorem exists_app_eq [ConnectedSpace X] :
    ∃ m : Λ, ∀ {Y : Scheme.{u}} (y : Y ⟶ X) (χ : Multiplicative Λ →* Γ(Y, ⊤)ˣ),
      c.app y χ = χ (.ofAdd m) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨m, hm⟩ := c.exists_mem_locus x
  have h := IsClopen.eq_univ ⟨c.isClosed_locus m, c.isOpen_locus m⟩ ⟨x, hm⟩
  exact ⟨m, fun y χ => c.app_eq_of_locus (fun x' => h ▸ Set.mem_univ x') y χ⟩

end CharFamily

/-! ### From a morphism `X × G → H` to families of characters -/

section Assembly

variable {R : CommRingCat.{u}} {Λ Λ' : Type u} [AddCommGroup Λ] [AddCommGroup Λ']
  {G H : GroupScheme (Spec R)} (eG : G ≅ (Diagonalizable.groupScheme R Λ).toGrp)
  (eH : H ≅ (Diagonalizable.groupScheme R Λ').toGrp) {X : Over (Spec R)}
  (φ : X ⊗ G.X ⟶ H.X)
  (hφ : ∀ (T : Over (Spec R)) (x : T ⟶ X) (g g' : T ⟶ G.X),
    lift x (g * g') ≫ φ = (lift x g ≫ φ) * (lift x g' ≫ φ))

/-- The homomorphism `D(Λ)(T) → D(Λ')(T)` at the parameter `x`, transported along `eG`, `eH`. -/
def pointHom {T : Over (Spec R)} (x : T ⟶ X) :
    (T ⟶ (Diagonalizable.groupScheme R Λ).X) →* (T ⟶ (Diagonalizable.groupScheme R Λ').X) :=
  MonoidHom.mk' (fun g => lift x (g ≫ eG.inv.hom.hom) ≫ φ ≫ eH.hom.hom.hom) fun g g' => by
    have h := hφ T x (g ≫ eG.inv.hom.hom) (g' ≫ eG.inv.hom.hom)
    simp only [← Category.assoc, MonObj.mul_comp, h]

theorem pointHom_apply {T : Over (Spec R)} (x : T ⟶ X)
    (g : T ⟶ (Diagonalizable.groupScheme R Λ).X) :
    pointHom eG eH φ hφ x g = lift x (g ≫ eG.inv.hom.hom) ≫ φ ≫ eH.hom.hom.hom :=
  rfl

theorem pointHom_comp {T T' : Over (Spec R)} (a : T' ⟶ T) (x : T ⟶ X)
    (g : T ⟶ (Diagonalizable.groupScheme R Λ).X) :
    pointHom eG eH φ hφ (a ≫ x) (a ≫ g) = a ≫ pointHom eG eH φ hφ x g := by
  rw [pointHom_apply, pointHom_apply, ← Category.assoc a, comp_lift]
  simp only [Category.assoc]

/-- The `l`-th coordinate of the family, as a family of characters parametrized by `X`. -/
def family (l : Λ') : CharFamily X.left Λ where
  app {Y} y :=
    { toFun := fun χ => Diagonalizable.characterPointsEquiv R Λ' (Over.mk (y ≫ X.hom))
        (pointHom eG eH φ hφ (Over.homMk y : Over.mk (y ≫ X.hom) ⟶ X)
          ((Diagonalizable.characterPointsEquiv R Λ (Over.mk (y ≫ X.hom))).symm χ)) (.ofAdd l)
      map_one' := by
        simp only [map_one]
        rfl
      map_mul' := fun χ χ' => by
        simp only [map_mul]
        rfl }
  naturality {Y Y'} t y χ := by
    let a : Over.mk ((t ≫ y) ≫ X.hom) ⟶ Over.mk (y ≫ X.hom) := Over.homMk t (by simp)
    have h1 : (Over.homMk (t ≫ y) : Over.mk ((t ≫ y) ≫ X.hom) ⟶ X) =
        a ≫ Over.homMk y := by
      ext
      simp [a]
    have h2 : (Diagonalizable.characterPointsEquiv R Λ (Over.mk ((t ≫ y) ≫ X.hom))).symm
        (resChar t χ) =
          a ≫ (Diagonalizable.characterPointsEquiv R Λ (Over.mk (y ≫ X.hom))).symm χ := by
      apply (Diagonalizable.characterPointsEquiv R Λ _).injective
      rw [MulEquiv.apply_symm_apply, characterPointsEquiv_comp, MulEquiv.apply_symm_apply]
      rfl
    change Diagonalizable.characterPointsEquiv R Λ' (Over.mk ((t ≫ y) ≫ X.hom))
        (pointHom eG eH φ hφ (Over.homMk (t ≫ y))
          ((Diagonalizable.characterPointsEquiv R Λ (Over.mk ((t ≫ y) ≫ X.hom))).symm
            (resChar t χ))) (.ofAdd l) =
      Units.map t.appTop.hom.toMonoidHom
        (Diagonalizable.characterPointsEquiv R Λ' (Over.mk (y ≫ X.hom))
          (pointHom eG eH φ hφ (Over.homMk y)
            ((Diagonalizable.characterPointsEquiv R Λ (Over.mk (y ≫ X.hom))).symm χ)) (.ofAdd l))
    rw [h1, h2, pointHom_comp, Diagonalizable.characterPointsEquiv_naturality]
    rfl

/-- The coordinates of `φ(x, g)` are the values of the families at `x`. -/
theorem family_app (l : Λ') {T : Over (Spec R)} (x : T ⟶ X) (g : T ⟶ G.X) :
    Diagonalizable.characterPointsEquiv R Λ' T (lift x g ≫ φ ≫ eH.hom.hom.hom) (.ofAdd l) =
      (family eG eH φ hφ l).app x.left
        (Diagonalizable.characterPointsEquiv R Λ T (g ≫ eG.hom.hom.hom)) := by
  let e : T ⟶ Over.mk (x.left ≫ X.hom) := Over.homMk (𝟙 T.left) (by simp [Over.w x])
  have hx : e ≫ (Over.homMk x.left : Over.mk (x.left ≫ X.hom) ⟶ X) = x := by
    ext
    simp [e]
  have hg' : e ≫ (Diagonalizable.characterPointsEquiv R Λ (Over.mk (x.left ≫ X.hom))).symm
      (Diagonalizable.characterPointsEquiv R Λ T (g ≫ eG.hom.hom.hom)) = g ≫ eG.hom.hom.hom := by
    apply (Diagonalizable.characterPointsEquiv R Λ T).injective
    rw [characterPointsEquiv_comp, MulEquiv.apply_symm_apply]
    ext l
    simp [e]
  have hg : e ≫ (Diagonalizable.characterPointsEquiv R Λ (Over.mk (x.left ≫ X.hom))).symm
      (Diagonalizable.characterPointsEquiv R Λ T (g ≫ eG.hom.hom.hom)) ≫ eG.inv.hom.hom = g := by
    rw [← Category.assoc, hg', Category.assoc, ← Grp.comp_hom_hom, eG.hom_inv_id,
      Grp.id_hom_hom, Category.comp_id]
  have key : lift x g ≫ φ ≫ eH.hom.hom.hom = e ≫ pointHom eG eH φ hφ
      (Over.homMk x.left : Over.mk (x.left ≫ X.hom) ⟶ X)
      ((Diagonalizable.characterPointsEquiv R Λ (Over.mk (x.left ≫ X.hom))).symm
        (Diagonalizable.characterPointsEquiv R Λ T (g ≫ eG.hom.hom.hom))) := by
    rw [← pointHom_comp, pointHom_apply, hx, Category.assoc, hg]
  rw [key, Diagonalizable.characterPointsEquiv_naturality]
  change Units.map (𝟙 T.left : T.left ⟶ T.left).appTop.hom.toMonoidHom _ = _
  simp
  rfl

include eG eH hφ in
/-- **Rigidity on an arbitrary affine base.** The value `φ(x, g)` does not depend on the
parameter `x` when `X` is connected. -/
theorem eq_of_connected [ConnectedSpace X.left] {T : Over (Spec R)} (x x' : T ⟶ X)
    (g : T ⟶ G.X) : lift x g ≫ φ = lift x' g ≫ φ := by
  have key : lift x g ≫ φ ≫ eH.hom.hom.hom = lift x' g ≫ φ ≫ eH.hom.hom.hom := by
    apply (Diagonalizable.characterPointsEquiv R Λ' T).injective
    apply MonoidHom.ext
    intro l
    obtain ⟨m, hm⟩ := (family eG eH φ hφ l.toAdd).exists_app_eq
    have h1 := family_app eG eH φ hφ l.toAdd x g
    have h2 := family_app eG eH φ hφ l.toAdd x' g
    rw [hm] at h1 h2
    exact h1.trans h2.symm
  have := congrArg (· ≫ eH.inv.hom.hom) key
  simp only [Category.assoc] at this
  rwa [← Grp.comp_hom_hom, eH.hom_inv_id, Grp.id_hom_hom, Category.comp_id] at this

end Assembly

end DiagonalizableRigidity

/-- **Rigidity of diagonalizable groups** (Milne, *Algebraic Groups* (2017), Theorem 12.36). -/
theorem diagonalizableRigidity : DiagonalizableRigidityStatement.{u} := by
  intro k _ G H Λ Λ' _ _ _ _ hG hH X _ _ _ φ hφ x₀ T x g
  obtain ⟨eG⟩ := hG
  obtain ⟨eH⟩ := hH
  exact DiagonalizableRigidity.eq_of_connected eG eH φ hφ x (toUnit T ≫ x₀) g

end Langlands.GroupScheme
