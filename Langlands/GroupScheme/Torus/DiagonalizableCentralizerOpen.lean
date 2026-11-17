import Langlands.GroupScheme.Torus.DiagonalizableCharacterProof
import Langlands.GroupScheme.Rational.TorusNormalizerRigidity
import Langlands.GroupScheme.Dynamic.Functoriality

/-! # The centralizer of a diagonalizable subgroup is open in its normalizer

Let `i : H ⟶ G` be a monomorphism of group schemes over `Spec R` with `H ≅ D(Λ)` for a finitely
generated abelian group `Λ` (torsion allowed). A point `g` of the normalizer of `H` acts on the
characters of `H` by conjugation. Over an affine chart `Spec R' ⟶ U`, conjugation on each
generator `ν` of `Λ` is a natural family of units on the points of `D(Λ)`, whose universal value
is a grouplike element of `R'[Λ]`; conjugation is trivial exactly where the idempotent
coefficients at the generators are `1`. This gives an open locus `centralizerLocus` in the
parameter scheme of `g`, and a represented centralizer inside a represented normalizer is the
open subscheme cut out by this locus. -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace DiagonalizableConjugation

open DiagonalizableCharacter

section Algebra

variable {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]

/-- If the coefficient of `m` in the universal value of `c` becomes `1` in `Γ(U)`, then `c` is
evaluation at `m` on every point over `U`. -/
theorem app_eq_of_coeff (c : NaturalUnits R Λ) (m : Λ) (U : Over (Spec R))
    (he : U.hom.appTop ((Scheme.ΓSpecIso R).inv (c.value.coeff m)) = 1)
    (x : U ⟶ (Diagonalizable.groupScheme R Λ).X) :
    c.app U x = Diagonalizable.characterPointsEquiv R Λ U x (.ofAdd m) := by
  classical
  let B : CommAlgCat.{u} R := ((algΓ R).obj U).unop
  have he' : algebraMap R B (c.value.coeff m) = 1 := he
  apply Units.ext
  rw [c.app_eq]
  have hg := c.isGrouplike_value
  set t := Diagonalizable.characterPointsEquiv R Λ U x
  change AddMonoidAlgebra.lift R B Λ ((Units.coeHom B).comp t) c.value = _
  rw [AddMonoidAlgebra.lift_apply']
  rw [Finsupp.sum_eq_single m]
  · rw [he', one_mul]
    rfl
  · intro ν _ hν
    have h0 : c.value.coeff ν * c.value.coeff m = 0 := hg.coeff_mul_coeff_of_ne hν.symm
    have h1 : algebraMap R B (c.value.coeff ν) = 0 := by
      have := congrArg (algebraMap R B) h0
      rwa [map_mul, he', mul_one, map_zero] at this
    rw [h1, zero_mul]
  · intro _
    rw [map_zero, zero_mul]

/-- Evaluating at the universal monomial character of `A[Λ]` is the coefficient change. -/
theorem lift_of_eq_mapRingHom (A : Type u) [CommRing A] [Algebra R A]
    (v : AddMonoidAlgebra R Λ) :
    (Diagonalizable.lift R Λ (B := CommAlgCat.of R (AddMonoidAlgebra A Λ))
      (AddMonoidAlgebra.of A Λ).toHomUnits).hom v =
      AddMonoidAlgebra.mapRingHom Λ (algebraMap R A) v := by
  induction v using AddMonoidAlgebra.induction_linear with
  | zero => simp only [map_zero]
  | add v w hv hw => rw [map_add, map_add, hv, hw]
  | single ν r =>
    rw [Diagonalizable.lift_single]
    change r • AddMonoidAlgebra.single ν (1 : A) = _
    rw [AddMonoidAlgebra.mapRingHom_single, AddMonoidAlgebra.smul_single,
      Algebra.smul_def, mul_one]

/-- Detection of the coefficient: if `c` is evaluation at `m` at the universal character over
`A[Λ]`, then the coefficient of `m` in its universal value becomes `1` in `A`. -/
theorem coeff_eq_one_of_app (c : NaturalUnits R Λ) (m : Λ) (A : Type u) [CommRing A]
    [Algebra R A]
    (h : c.app (NaturalUnits.affine (CommAlgCat.of R (AddMonoidAlgebra A Λ)))
        (NaturalUnits.affinePoint (CommAlgCat.of R (AddMonoidAlgebra A Λ))
          (AddMonoidAlgebra.of A Λ).toHomUnits) =
      Diagonalizable.characterPointsEquiv R Λ _
        (NaturalUnits.affinePoint (CommAlgCat.of R (AddMonoidAlgebra A Λ))
          (AddMonoidAlgebra.of A Λ).toHomUnits) (.ofAdd m)) :
    algebraMap R A (c.value.coeff m) = 1 := by
  set B := CommAlgCat.of R (AddMonoidAlgebra A Λ)
  have h₁ := c.toSections_lift B (AddMonoidAlgebra.of A Λ).toHomUnits
  rw [h] at h₁
  have hpt : Diagonalizable.characterPointsEquiv R Λ (NaturalUnits.affine B)
      (NaturalUnits.affinePoint B (AddMonoidAlgebra.of A Λ).toHomUnits) =
      (Units.map (NaturalUnits.toSections B).hom.toRingHom.toMonoidHom).comp
        (AddMonoidAlgebra.of A Λ).toHomUnits :=
    (Diagonalizable.characterPointsEquiv R Λ (NaturalUnits.affine B)).apply_symm_apply _
  have h₂ : (Diagonalizable.lift R Λ (B := B) (AddMonoidAlgebra.of A Λ).toHomUnits).hom c.value =
      AddMonoidAlgebra.single m 1 := by
    apply NaturalUnits.toSections_injective B
    rw [h₁, hpt]
    rfl
  rw [lift_of_eq_mapRingHom] at h₂
  have h₄ := congrArg (fun w : AddMonoidAlgebra A Λ => w.coeff m) h₂
  simpa using h₄

end Algebra

section Characters

variable {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]

variable (Λ) in
/-- Characters of `Λ` with values in the global units of a scheme. -/
abbrev Chars (X : Scheme.{u}) : Type u := Multiplicative Λ →* (Γ(X, ⊤))ˣ

/-- Restriction of characters along a morphism of schemes. -/
def charsRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (x : Chars Λ Y) : Chars Λ X :=
  (Units.map f.appTop.hom.toMonoidHom).comp x

theorem charsRestrict_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (x : Chars Λ Y)
    (b : Multiplicative Λ) :
    charsRestrict f x b = Units.map f.appTop.hom.toMonoidHom (x b) := rfl

/-- The character model of the points of `D(Λ)` is natural. -/
theorem characterPointsEquiv_comp {V V' : Over (Spec R)} (c : V' ⟶ V)
    (x : V ⟶ (Diagonalizable.groupScheme R Λ).X) :
    Diagonalizable.characterPointsEquiv R Λ V' (c ≫ x) =
      charsRestrict c.left (Diagonalizable.characterPointsEquiv R Λ V x) :=
  MonoidHom.ext fun b =>
    Diagonalizable.characterPointsEquiv_naturality R Λ c x (Multiplicative.toAdd b)

theorem comp_characterPointsEquiv_symm {V V' : Over (Spec R)} (c : V' ⟶ V)
    (x : Chars Λ V.left) :
    c ≫ (Diagonalizable.characterPointsEquiv R Λ V).symm x =
      (Diagonalizable.characterPointsEquiv R Λ V').symm (charsRestrict c.left x) := by
  apply (Diagonalizable.characterPointsEquiv R Λ V').injective
  rw [characterPointsEquiv_comp, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

variable (Λ) in
/-- A chosen finite generating set of a finitely generated abelian group. -/
def gens [AddGroup.FG Λ] : Finset Λ :=
  (AddGroup.FG.out (H := Λ)).choose

theorem closure_gens [AddGroup.FG Λ] : AddSubgroup.closure (gens Λ : Set Λ) = ⊤ :=
  (AddGroup.FG.out (H := Λ)).choose_spec

/-- Characters agreeing on the chosen generators are equal. -/
theorem chars_ext [AddGroup.FG Λ] {X : Scheme.{u}} {x y : Chars Λ X}
    (h : ∀ ν ∈ gens Λ, x (.ofAdd ν) = y (.ofAdd ν)) : x = y := by
  refine MonoidHom.eq_of_eqOn_dense (s := Multiplicative.toAdd ⁻¹' (gens Λ : Set Λ)) ?_ ?_
  · rw [← AddSubgroup.toSubgroup_closure, closure_gens]
    rfl
  · intro b hb
    exact h (Multiplicative.toAdd b) hb

end Characters


section Points

variable {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]
  {G H : GroupScheme (Spec R)} (i : H ⟶ G) (e : H ≅ (Diagonalizable.groupScheme R Λ).toGrp)

/-- The point of `G` given by the point of `H ≅ D(Λ)` with character `x`. -/
def charPoint (V : Over (Spec R)) (x : Chars Λ V.left) : V ⟶ G.X :=
  ((Diagonalizable.characterPointsEquiv R Λ V).symm x ≫ e.inv.hom.hom) ≫ i.hom.hom

theorem charPoint_mul (V : Over (Spec R)) (x y : Chars Λ V.left) :
    charPoint i e V (x * y) = charPoint i e V x * charPoint i e V y := by
  simp only [charPoint, map_mul, MonObj.mul_comp]

theorem comp_charPoint {V V' : Over (Spec R)} (c : V' ⟶ V) (x : Chars Λ V.left) :
    c ≫ charPoint i e V x = charPoint i e V' (charsRestrict c.left x) := by
  rw [charPoint, charPoint, ← Category.assoc, ← Category.assoc,
    comp_characterPointsEquiv_symm]

/-- Every point of `H` is a character point. -/
theorem comp_eq_charPoint (V : Over (Spec R)) (t : V ⟶ H.X) :
    t ≫ i.hom.hom =
      charPoint i e V (Diagonalizable.characterPointsEquiv R Λ V (t ≫ e.hom.hom.hom)) := by
  rw [charPoint, MulEquiv.symm_apply_apply, Category.assoc t, ← Grp.comp_hom_hom e.hom e.inv,
    e.hom_inv_id, Grp.id_hom_hom, Category.comp_id]

theorem charPoint_injective [Mono i.hom.hom.left] (V : Over (Spec R)) :
    Function.Injective (charPoint i e V) := by
  intro x y h
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : IsIso e.inv.hom.hom :=
    (inferInstance : IsIso ((Grp.forget (Over (Spec R))).mapIso e.symm).hom)
  rw [charPoint, charPoint, cancel_mono, cancel_mono] at h
  exact (Diagonalizable.characterPointsEquiv R Λ V).symm.injective h

theorem charPoint_mem (V : Over (Spec R)) (x : Chars Λ V.left) :
    charPoint i e V x ∈ (SubgroupFunctor.range i).carrier V :=
  SubgroupFunctor.mem_range.2 ⟨_, rfl⟩

variable {i} {U : Over (Spec R)} {g : U ⟶ G.X}

theorem exists_conj_charPoint (hg : g ∈ (SubgroupFunctor.range i).normalizer.carrier U)
    {V : Over (Spec R)} (a : V ⟶ U) (x : Chars Λ V.left) :
    ∃ y, (a ≫ g) * charPoint i e V x * (a ≫ g)⁻¹ = charPoint i e V y := by
  obtain ⟨t, ht⟩ := SubgroupFunctor.mem_range.1 (hg V a _ (charPoint_mem i e V x)).1
  exact ⟨_, ht.symm.trans (comp_eq_charPoint i e V t)⟩

variable (hg : g ∈ (SubgroupFunctor.range i).normalizer.carrier U)

/-- The character of the conjugate by `a ≫ g` of the character point `x`. -/
def conjChars {V : Over (Spec R)} (a : V ⟶ U) (x : Chars Λ V.left) : Chars Λ V.left :=
  (exists_conj_charPoint e hg a x).choose

theorem conjChars_spec {V : Over (Spec R)} (a : V ⟶ U) (x : Chars Λ V.left) :
    (a ≫ g) * charPoint i e V x * (a ≫ g)⁻¹ = charPoint i e V (conjChars e hg a x) :=
  (exists_conj_charPoint e hg a x).choose_spec

/-- `conjChars` only depends on the underlying morphism of schemes. -/
theorem conjChars_congr {X : Scheme.{u}} {s₁ s₂ : X ⟶ Spec R} (b₁ : Over.mk s₁ ⟶ U)
    (b₂ : Over.mk s₂ ⟶ U) (h : b₁.left = b₂.left) :
    conjChars e hg b₁ = conjChars e hg b₂ := by
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

theorem conjChars_eq_iff {V : Over (Spec R)} (a : V ⟶ U) (x y : Chars Λ V.left) :
    conjChars e hg a x = y ↔
      (a ≫ g) * charPoint i e V x * (a ≫ g)⁻¹ = charPoint i e V y := by
  rw [conjChars_spec e hg a x, (charPoint_injective i e V).eq_iff]

theorem conjChars_mul {V : Over (Spec R)} (a : V ⟶ U) (x y : Chars Λ V.left) :
    conjChars e hg a (x * y) = conjChars e hg a x * conjChars e hg a y := by
  rw [conjChars_eq_iff, charPoint_mul, charPoint_mul, ← conjChars_spec, ← conjChars_spec]
  group

/-- Conjugation as a homomorphism of character groups. -/
def conjCharsHom {V : Over (Spec R)} (a : V ⟶ U) : Chars Λ V.left →* Chars Λ V.left :=
  MonoidHom.mk' (conjChars e hg a) (conjChars_mul e hg a)

theorem conjChars_naturality {V V' : Over (Spec R)} (c : V' ⟶ V) (a : V ⟶ U)
    (x : Chars Λ V.left) :
    conjChars e hg (c ≫ a) (charsRestrict c.left x) =
      charsRestrict c.left (conjChars e hg a x) := by
  rw [conjChars_eq_iff, ← comp_charPoint, ← comp_charPoint, ← conjChars_spec]
  simp only [MonObj.comp_mul, GrpObj.comp_inv, Category.assoc]

/-- Conjugation by `g` is trivial on `H` over every test scheme over `V`. -/
def ActsTrivially {V : Over (Spec R)} (a : V ⟶ U) : Prop :=
  ∀ (V' : Over (Spec R)) (c : V' ⟶ V) (x : Chars Λ V'.left), conjChars e hg (c ≫ a) x = x

omit [Mono i.hom.hom.left] in
theorem ActsTrivially.comp {V V' : Over (Spec R)} {a : V ⟶ U} (h : ActsTrivially e hg a)
    (c : V' ⟶ V) : ActsTrivially e hg (c ≫ a) := by
  intro W d x
  rw [← Category.assoc]
  exact h W (d ≫ c) x

omit [Mono i.hom.hom.left] in
theorem actsTrivially_congr {X : Scheme.{u}} {s₁ s₂ : X ⟶ Spec R}
    (b₁ : Over.mk s₁ ⟶ U) (b₂ : Over.mk s₂ ⟶ U) (h : b₁.left = b₂.left) :
    ActsTrivially e hg b₁ ↔ ActsTrivially e hg b₂ := by
  have hs : s₁ = s₂ := by
    have h₁ := Over.w b₁
    have h₂ := Over.w b₂
    simp only [Over.mk_hom] at h₁ h₂
    rw [← h₁, ← h₂, h]
  subst hs
  have : b₁ = b₂ := Over.OverMorphism.ext h
  subst this
  rfl

/-- Acting trivially is centralizing `H`. -/
theorem actsTrivially_iff {V : Over (Spec R)} (a : V ⟶ U) :
    ActsTrivially e hg a ↔ a ≫ g ∈ (SubgroupFunctor.range i).centralizer.carrier V := by
  rw [SubgroupFunctor.mem_centralizer]
  constructor
  · intro h V' c x hx
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    rw [comp_eq_charPoint i e V' t]
    have h' := (conjChars_eq_iff e hg (c ≫ a) _ _).1
      (h V' c (Diagonalizable.characterPointsEquiv R Λ V' (t ≫ e.hom.hom.hom)))
    rw [Category.assoc] at h'
    exact mul_inv_eq_iff_eq_mul.1 h'
  · intro h V' c x
    rw [conjChars_eq_iff, Category.assoc]
    exact mul_inv_eq_of_eq_mul (h V' c (charPoint i e V' x) (charPoint_mem i e V' x)).eq

end Points

section Charts

variable {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]
  {G H : GroupScheme (Spec R)} {i : H ⟶ G}
  (e : H ≅ (Diagonalizable.groupScheme R Λ).toGrp)
  {U : Over (Spec R)} {g : U ⟶ G.X} (hg : g ∈ (SubgroupFunctor.range i).normalizer.carrier U)
  {R' : CommRingCat.{u}} {s : Spec R' ⟶ Spec R}

/-- It suffices to test triviality over schemes presented as `Over.mk s`. -/
theorem actsTrivially_of_forall_mk {V : Over (Spec R)} (a : V ⟶ U)
    (h : ∀ (X : Scheme.{u}) (s : X ⟶ Spec R) (b : Over.mk s ⟶ V) (x : Chars Λ X),
      conjChars e hg (b ≫ a) x = x) : ActsTrivially e hg a :=
  fun V' c x => h V'.left V'.hom c x

/-- It suffices to test triviality over affine schemes. -/
theorem actsTrivially_of_forall_affine [Mono i.hom.hom.left] {V : Over (Spec R)} (a : V ⟶ U)
    (h : ∀ (A : CommRingCat.{u}) (s : Spec A ⟶ Spec R) (b : Over.mk s ⟶ V)
      (x : Chars Λ (Spec A)), conjChars e hg (b ≫ a) x = x) :
    ActsTrivially e hg a := by
  intro V' c x
  apply (Diagonalizable.characterPointsEquiv R Λ V').symm.injective
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext V'.left.affineOpenCover.openCover _ _ fun j => ?_
  let d : Over.mk (V'.left.affineOpenCover.f j ≫ V'.hom) ⟶ V' :=
    Over.homMk (V'.left.affineOpenCover.f j)
  have key : d ≫ (Diagonalizable.characterPointsEquiv R Λ V').symm (conjChars e hg (c ≫ a) x) =
      d ≫ (Diagonalizable.characterPointsEquiv R Λ V').symm x := by
    rw [comp_characterPointsEquiv_symm, comp_characterPointsEquiv_symm,
      ← conjChars_naturality, ← Category.assoc, h _ _ (d ≫ c)]
  exact congrArg (fun f => f.left) key

/-- The point of `U` over a scheme `W` over the chart `Spec R'`. -/
def chartHom (ρ : Over.mk s ⟶ U) (W : Over (Spec R')) : Over.mk (W.hom ≫ s) ⟶ U :=
  (Over.homMk W.hom : Over.mk (W.hom ≫ s) ⟶ Over.mk s) ≫ ρ

theorem chartHom_left (ρ : Over.mk s ⟶ U) (W : Over (Spec R')) :
    (chartHom ρ W).left = W.hom ≫ ρ.left := rfl

/-- The comparison map between test schemes over the chart. -/
abbrev chartMap {W W' : Over (Spec R')} (a : W' ⟶ W) :
    Over.mk (W'.hom ≫ s) ⟶ Over.mk (W.hom ≫ s) :=
  Over.homMk a.left (by
    simp only [Over.mk_hom]
    rw [← Over.w a, Category.assoc])

theorem chartMap_comp_chartHom (ρ : Over.mk s ⟶ U) {W W' : Over (Spec R')} (a : W' ⟶ W) :
    chartMap (s := s) a ≫ chartHom ρ W = chartHom ρ W' := by
  apply Over.OverMorphism.ext
  change a.left ≫ W.hom ≫ ρ.left = W'.hom ≫ ρ.left
  rw [← Category.assoc, Over.w a]

variable [Mono i.hom.hom.left]

/-- Conjugation by `g` on the character `ν`, through the chart `ρ`, as a natural family of
units on the points of `D(Λ)` over `Spec R'`. -/
def chartUnits (ρ : Over.mk s ⟶ U) (ν : Λ) : NaturalUnits R' Λ where
  app W := MonoidHom.mk'
    (fun x => conjChars e hg (chartHom ρ W)
      (Diagonalizable.characterPointsEquiv R' Λ W x) (.ofAdd ν))
    (fun x y => by
      simp only [map_mul]
      rw [conjChars_mul, MonoidHom.mul_apply])
  naturality {W W'} a x := by
    have h := conjChars_naturality e hg (chartMap (s := s) a) (chartHom ρ W)
      (Diagonalizable.characterPointsEquiv R' Λ W x)
    rw [chartMap_comp_chartHom] at h
    simp only [MonoidHom.mk'_apply]
    rw [characterPointsEquiv_comp]
    exact congrArg (fun y : Chars Λ W'.left => y (.ofAdd ν)) h

theorem chartUnits_app (ρ : Over.mk s ⟶ U) (ν : Λ) (W : Over (Spec R'))
    (x : W ⟶ (Diagonalizable.groupScheme R' Λ).X) :
    (chartUnits e hg ρ ν).app W x = conjChars e hg (chartHom ρ W)
      (Diagonalizable.characterPointsEquiv R' Λ W x) (.ofAdd ν) := rfl

theorem isIdempotentElem_chartCoeff (ρ : Over.mk s ⟶ U) (ν : Λ) :
    IsIdempotentElem ((chartUnits e hg ρ ν).value.coeff ν) :=
  (chartUnits e hg ρ ν).isGrouplike_value.isIdempotentElem_coeff ν

variable [AddGroup.FG Λ]

/-- Over a test scheme on which the coefficients become `1`, conjugation is trivial. -/
theorem actsTrivially_chartHom (ρ : Over.mk s ⟶ U) (W : Over (Spec R'))
    (hW : ∀ ν ∈ gens Λ, W.hom.appTop ((Scheme.ΓSpecIso R').inv
      ((chartUnits e hg ρ ν).value.coeff ν)) = 1) :
    ActsTrivially e hg (chartHom ρ W) := by
  apply actsTrivially_of_forall_mk
  intro X s' b x
  let W' : Over (Spec R') := Over.mk (b.left ≫ W.hom)
  rw [conjChars_congr e hg (b ≫ chartHom ρ W) (chartHom ρ W')
    (by simp only [Over.comp_left, chartHom_left, W', Over.mk_hom, Category.assoc])]
  apply chars_ext
  intro ν hν
  have hW' : W'.hom.appTop ((Scheme.ΓSpecIso R').inv
      ((chartUnits e hg ρ ν).value.coeff ν)) = 1 := by
    change (b.left ≫ W.hom).appTop _ = 1
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    exact (congrArg (fun r => b.left.appTop.hom r) (hW ν hν)).trans (map_one _)
  have h := app_eq_of_coeff (chartUnits e hg ρ ν) ν W' hW'
    ((Diagonalizable.characterPointsEquiv R' Λ W').symm x)
  rw [chartUnits_app, MulEquiv.apply_symm_apply] at h
  exact h

/-- The point of `U` over `Spec B` obtained from the chart `ρ` and a ring map `β : R' ⟶ B`. -/
abbrev chartPoint (ρ : Over.mk s ⟶ U) {B : CommRingCat.{u}} (β : R' ⟶ B) :
    Over.mk (Spec.map β ≫ s) ⟶ U :=
  chartHom ρ (Over.mk (Spec.map β))

theorem actsTrivially_chartPoint_iff (ρ : Over.mk s ⟶ U) {B : CommRingCat.{u}} (β : R' ⟶ B) :
    ActsTrivially e hg (chartPoint ρ β) ↔
      ∀ ν ∈ gens Λ, β ((chartUnits e hg ρ ν).value.coeff ν) = 1 := by
  constructor
  · intro h ν _
    let : Algebra R' B := β.hom.toAlgebra
    let P : CommAlgCat.{u} R' := CommAlgCat.of R' (AddMonoidAlgebra B Λ)
    let W := NaturalUnits.affine P
    have hw : Spec.map (CommRingCat.ofHom (algebraMap B (AddMonoidAlgebra B Λ))) ≫
        Spec.map β ≫ s = W.hom ≫ s := by
      rw [← Category.assoc, ← Spec.map_comp]
      rfl
    let c : Over.mk (W.hom ≫ s) ⟶ Over.mk (Spec.map β ≫ s) :=
      Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap B (AddMonoidAlgebra B Λ)))) hw
    have hc : c ≫ chartPoint ρ β = chartHom ρ W := by
      apply Over.OverMorphism.ext
      change Spec.map (CommRingCat.ofHom (algebraMap B (AddMonoidAlgebra B Λ))) ≫
          Spec.map β ≫ ρ.left = W.hom ≫ ρ.left
      rw [← Category.assoc, ← Spec.map_comp]
      rfl
    have hconj : ∀ y, conjChars e hg (chartHom ρ W) y = y := by
      intro y
      rw [← hc]
      exact h _ c y
    have happ := coeff_eq_one_of_app (chartUnits e hg ρ ν) ν B (by
      rw [chartUnits_app, hconj]
      rfl)
    exact happ
  · intro h
    apply actsTrivially_chartHom
    intro ν hν
    change (Spec.map β).appTop _ = 1
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply,
      h ν hν, map_one]

theorem actsTrivially_chart_iff (ρ : Over.mk s ⟶ U) :
    ActsTrivially e hg ρ ↔ ∀ ν ∈ gens Λ, (chartUnits e hg ρ ν).value.coeff ν = 1 := by
  rw [actsTrivially_congr e hg ρ (chartPoint ρ (𝟙 R'))
    (by
      simp only [chartHom_left, Over.mk_hom, Spec.map_id]
      exact (Category.id_comp _).symm),
    actsTrivially_chartPoint_iff]
  rfl

end Charts

section Locus

variable {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]
  {G H : GroupScheme (Spec R)} {i : H ⟶ G}
  (e : H ≅ (Diagonalizable.groupScheme R Λ).toGrp)
  {U : Over (Spec R)} {g : U ⟶ G.X} (hg : g ∈ (SubgroupFunctor.range i).normalizer.carrier U)

/-- A morphism of schemes into `U` as a morphism over `Spec R`. -/
abbrev overHom {X : Scheme.{u}} (y : X ⟶ U.left) : Over.mk (y ≫ U.hom) ⟶ U :=
  Over.homMk y

/-- Conjugation by `g` is trivial on `H` over the residue field at `x`. -/
def ActsAtPoint (x : U.left) : Prop :=
  ActsTrivially e hg (overHom (U := U) (U.left.fromSpecResidueField x))

variable [Mono i.hom.hom.left] [AddGroup.FG Λ]

theorem actsTrivially_overHom_iff {K : Type u} [Field K]
    (y : Spec (CommRingCat.of K) ⟶ U.left) :
    ActsTrivially e hg (overHom (U := U) y) ↔ ActsAtPoint e hg (y (IsLocalRing.closedPoint K)) := by
  let ψ := Scheme.descResidueField (Scheme.stalkClosedPointTo y)
  have hy : Spec.map ψ ≫ U.left.fromSpecResidueField (y (IsLocalRing.closedPoint K)) = y :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K U.left y
  let ρ := overHom (U := U) (U.left.fromSpecResidueField (y (IsLocalRing.closedPoint K)))
  rw [actsTrivially_congr e hg (overHom (U := U) y) (chartPoint ρ ψ)
    (by simp only [chartHom_left, Over.mk_hom, ρ, Over.homMk_left, hy]),
    actsTrivially_chartPoint_iff, ActsAtPoint, actsTrivially_chart_iff]
  refine forall₂_congr fun ν _ => ⟨fun h => ψ.hom.injective (by rw [h, map_one]), fun h => ?_⟩
  rw [h, map_one]

theorem actsAtPoint_chart_iff {R' : CommRingCat.{u}} {s : Spec R' ⟶ Spec R}
    (ρ : Over.mk s ⟶ U) (p : PrimeSpectrum R') :
    ActsAtPoint e hg (ρ.left p) ↔
      ∀ ν ∈ gens Λ, (chartUnits e hg ρ ν).value.coeff ν ∉ p.asIdeal := by
  let β : R' ⟶ CommRingCat.of p.asIdeal.ResidueField :=
    CommRingCat.ofHom (algebraMap R' p.asIdeal.ResidueField)
  have hβ : (Spec.map β) (IsLocalRing.closedPoint p.asIdeal.ResidueField) = p := by
    have h := PrimeSpectrum.residueField_comap p
    have hmem : PrimeSpectrum.comap (algebraMap R' p.asIdeal.ResidueField)
        (IsLocalRing.closedPoint p.asIdeal.ResidueField) ∈ ({p} : Set (PrimeSpectrum R')) :=
      h ▸ ⟨_, rfl⟩
    exact hmem
  have hpt : (Spec.map β ≫ ρ.left) (IsLocalRing.closedPoint p.asIdeal.ResidueField) =
      ρ.left p := by
    rw [Scheme.Hom.comp_apply, hβ]
    rfl
  rw [← hpt, ← actsTrivially_overHom_iff,
    actsTrivially_congr e hg (overHom (U := U) (Spec.map β ≫ ρ.left)) (chartPoint ρ β) rfl,
    actsTrivially_chartPoint_iff]
  exact forall₂_congr fun ν _ => TorusConjugation.algebraMap_residueField_eq_one_iff
    (isIdempotentElem_chartCoeff e hg ρ ν) p.asIdeal

/-- The locus where conjugation by `g` is trivial on `H` is open. -/
theorem isOpen_actsAtPoint : IsOpen {x : U.left | ActsAtPoint e hg x} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨k, p₀, hp₀⟩ : ∃ k p₀, U.left.affineOpenCover.f k p₀ = x :=
    ⟨_, U.left.affineOpenCover.covers x⟩
  subst hp₀
  let b := U.left.affineOpenCover.f k
  let ρ := overHom (U := U) b
  let O : Set (PrimeSpectrum (U.left.affineOpenCover.X k)) :=
    ⋂ ν ∈ gens Λ, (PrimeSpectrum.basicOpen ((chartUnits e hg ρ ν).value.coeff ν) : Set _)
  have hO : IsOpen O :=
    isOpen_biInter_finset fun ν _ => (PrimeSpectrum.basicOpen _).isOpen
  have hmem : ∀ p : PrimeSpectrum (U.left.affineOpenCover.X k),
      p ∈ O ↔ ActsAtPoint e hg (b p) := by
    intro p
    refine Iff.trans ?_ (actsAtPoint_chart_iff e hg ρ p).symm
    simp only [O, Set.mem_iInter, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
  refine ⟨b '' O, ?_, b.isOpenEmbedding.isOpenMap _ hO, ⟨p₀, (hmem p₀).2 hx, rfl⟩⟩
  rintro _ ⟨p, hp, rfl⟩
  exact (hmem p).1 hp

/-- A restricted conjugation is trivial exactly when it is so at every residue-field point. -/
theorem actsTrivially_iff_forall_actsAtPoint {V : Over (Spec R)} (a : V ⟶ U) :
    ActsTrivially e hg a ↔ ∀ x : V.left, ActsAtPoint e hg (a.left x) := by
  constructor
  · intro h x
    let y := V.left.fromSpecResidueField x ≫ a.left
    have hy : ActsTrivially e hg (overHom (U := U) y) := by
      rw [actsTrivially_congr e hg (overHom (U := U) y)
        (overHom (U := V) (V.left.fromSpecResidueField x) ≫ a) rfl]
      exact ActsTrivially.comp e hg h (overHom (U := V) (V.left.fromSpecResidueField x))
    have hpt := (actsTrivially_overHom_iff e hg y).1 hy
    change ActsAtPoint e hg
      (a.left ((V.left.fromSpecResidueField x)
        (IsLocalRing.closedPoint (V.left.residueField x)))) at hpt
    simpa only [Scheme.fromSpecResidueField_apply] using hpt
  · intro h
    apply actsTrivially_of_forall_affine
    intro A s' b x
    have hd : ∀ ν ∈ gens Λ, (chartUnits e hg (b ≫ a) ν).value.coeff ν = 1 := by
      intro ν hν
      have hu : IsUnit ((chartUnits e hg (b ≫ a) ν).value.coeff ν) := by
        by_contra hd
        obtain ⟨P, hP, hdP⟩ := exists_max_ideal_of_mem_nonunits hd
        exact (actsAtPoint_chart_iff e hg (b ≫ a) ⟨P, hP.isPrime⟩).1
          (h (b.left ⟨P, hP.isPrime⟩)) ν hν hdP
      have hid := isIdempotentElem_chartCoeff e hg (b ≫ a) ν
      exact hu.mul_left_cancel (by rw [hid.eq, mul_one])
    have hb := (actsTrivially_chart_iff e hg (b ≫ a)).2 hd _ (𝟙 _) x
    simpa only [Category.id_comp] using hb

/-- The open locus where conjugation by `g` is trivial on `H`. -/
def centralizerLocus : U.left.Opens :=
  ⟨{x | ActsAtPoint e hg x}, isOpen_actsAtPoint e hg⟩

/-- Factorization through the centralizer locus is exactly all-test centralization. -/
theorem range_subset_centralizerLocus_iff {V : Over (Spec R)} (a : V ⟶ U) :
    Set.range a.left ⊆ centralizerLocus e hg ↔
      a ≫ g ∈ (SubgroupFunctor.range i).centralizer.carrier V := by
  rw [← actsTrivially_iff e hg a, actsTrivially_iff_forall_actsAtPoint]
  exact Set.range_subset_iff

end Locus


end DiagonalizableConjugation


/-- **Openness of the centralizer.** Let `H ⟶ G` be a monomorphism of group schemes over an
affine scheme `Spec R`, with `H` isomorphic to the diagonalizable group `D(Λ)` of a finitely
generated abelian group `Λ`. A representative of the centralizer of `H`, taken inside a
representative of the normalizer of `H`, is an open immersion. -/
theorem diagonalizableCentralizer_isOpenImmersion_of_iso {R : CommRingCat.{u}} {Λ : Type u}
    [AddCommGroup Λ] [AddGroup.FG Λ] {G H N C : GroupScheme (Spec R)}
    (i : H ⟶ G) [Mono i.hom.hom.left] (e : H ≅ (Diagonalizable.groupScheme R Λ).toGrp)
    (n : N ⟶ G) (hnrep : (SubgroupFunctor.range i).normalizer.IsRepresentedBy n)
    (c : C ⟶ N) (hcrep : ((SubgroupFunctor.range i).centralizer.comap n).IsRepresentedBy c) :
    IsOpenImmersion c.hom.hom.left := by
  have hg : n.hom.hom ∈ (SubgroupFunctor.range i).normalizer.carrier N.X := by
    simpa only [SubgroupFunctor.IsRepresentedBy.pointsEquiv_apply_coe,
      Category.id_comp] using (hnrep.pointsEquiv N.X (𝟙 _)).property
  let V := DiagonalizableConjugation.centralizerLocus e hg
  have hcV : Set.range c.hom.hom.left ⊆ V := by
    apply (DiagonalizableConjugation.range_subset_centralizerLocus_iff e hg c.hom.hom).2
    simpa only [SubgroupFunctor.IsRepresentedBy.pointsEquiv_apply_coe,
      Category.id_comp, SubgroupFunctor.mem_comap] using
      (hcrep.pointsEquiv C.X (𝟙 _)).property
  let v : C.X.left ⟶ V := IsOpenImmersion.lift V.ι c.hom.hom.left
    (by simpa only [Scheme.Opens.range_ι] using hcV)
  have hv : v ≫ V.ι = c.hom.hom.left := IsOpenImmersion.lift_fac _ _ _
  let a : Over.mk (V.ι ≫ N.X.hom) ⟶ N.X := Over.homMk V.ι
  have ha : a ≫ n.hom.hom ∈ (SubgroupFunctor.range i).centralizer.carrier _ := by
    apply (DiagonalizableConjugation.range_subset_centralizerLocus_iff e hg a).1
    rintro _ ⟨x, rfl⟩
    exact x.property
  obtain ⟨d, hd⟩ : ∃ d : Over.mk (V.ι ≫ N.X.hom) ⟶ C.X, d ≫ c.hom.hom = a := by
    have hm : a ∈ (SubgroupFunctor.range c).carrier _ := by
      rw [hcrep.2]
      exact ha
    exact hm
  have hdc : d.left ≫ c.hom.hom.left = V.ι := congrArg (fun f => f.left) hd
  have : Mono c.hom.hom := hcrep.1
  have : Mono c.hom.hom.left := Over.mono_left_of_mono _
  let eC : C.X.left ≅ V :=
    { hom := v
      inv := d.left
      hom_inv_id := by
        rw [← cancel_mono c.hom.hom.left, Category.assoc, hdc, hv, Category.id_comp]
      inv_hom_id := by
        rw [← cancel_mono V.ι, Category.assoc, hv, hdc, Category.id_comp] }
  have : IsIso v := eC.isIso_hom
  rw [← hv]
  infer_instance

/-- The case of a monomorphism from `D(Λ)` itself, phrased with `torusNormalizer` and
`torusCentralizer`. -/
theorem diagonalizableCentralizer_isOpenImmersion_of_mono {R : CommRingCat.{u}} {Λ : Type u}
    [AddCommGroup Λ] [AddGroup.FG Λ] {G N C : GroupScheme (Spec R)}
    (i : (Diagonalizable.groupScheme R Λ).toGrp ⟶ G) (hi : Mono i.hom.hom.left)
    (n : N ⟶ G) (c : C ⟶ N) (hn : (torusNormalizer i).IsRepresentedBy n)
    (hc : ((torusCentralizer i).comap n).IsRepresentedBy c) :
    IsOpenImmersion c.hom.hom.left := by
  rw [torusCentralizer_eq_centralizer_range] at hc
  exact diagonalizableCentralizer_isOpenImmersion_of_iso i (Iso.refl _) n hn c hc

/-- The field case, in the form of `DiagonalizableCentralizerOpenProperty`: for every field
`k`, every finitely generated abelian group `M` and every monomorphism `D(M) ⟶ G`, a
represented centralizer inside a represented normalizer is an open subgroup. -/
theorem diagonalizableCentralizer_isOpenImmersion_field (k : Type u) [Field k] (M : Type u)
    [AddCommGroup M] [AddGroup.FG M] (G N C : GroupScheme (Spec (CommRingCat.of k)))
    (i : (Diagonalizable.groupScheme (CommRingCat.of k) M).toGrp ⟶ G)
    (hi : Mono i.hom.hom.left) (n : N ⟶ G) (c : C ⟶ N)
    (hn : (torusNormalizer i).IsRepresentedBy n)
    (hc : ((torusCentralizer i).comap n).IsRepresentedBy c) :
    IsOpenImmersion c.hom.hom.left :=
  diagonalizableCentralizer_isOpenImmersion_of_mono i hi n c hn hc

end Langlands.GroupScheme
