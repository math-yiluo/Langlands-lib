import Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBaseTools
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteLimit
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsLocal
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsAffine
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalStepParts

/-! # Stalks of the representing schemes over the thickened closed point

For Step 2a of Murre's induction (Bourbaki exp. 294): if the base change of `F` along a
monomorphism `π : T₀ ⟶ Spec R` is represented by `q : Y ⟶ T₀`, the stalk of `Y` at a point,
with its element of `F`, classifies the elements of `F` over local rings whose classifying
morphism sends the closed point to that point. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace CompleteLocal

open Charts

variable {R : CommRingCat.{u}} (F : (Over (Spec R))ᵒᵖ ⥤ Type v)

section Level

variable {T₀ : Scheme.{u}} (π : T₀ ⟶ Spec R) {Y : Scheme.{u}} (q : Y ⟶ T₀) (y : Y)

/-- The stalk of `Y` at `y`, as a type (an `R`-algebra through `Y ⟶ T₀ ⟶ Spec R`). -/
@[nolint unusedArguments]
def LevelRing (_ : T₀ ⟶ Spec R) {Y : Scheme.{u}} (_ : Y ⟶ T₀) (y : Y) : Type u :=
  Y.presheaf.stalk y

instance : CommRing (LevelRing π q y) := inferInstanceAs (CommRing (Y.presheaf.stalk y))

instance : IsLocalRing (LevelRing π q y) := inferInstanceAs (IsLocalRing (Y.presheaf.stalk y))

/-- The ring map `R → 𝒪_{Y,y}` with spectrum `Spec 𝒪_{Y,y} ⟶ Y ⟶ T₀ ⟶ Spec R`. -/
def levelHom : R ⟶ Y.presheaf.stalk y :=
  (Spec.map_surjective (Y.fromSpecStalk y ≫ q ≫ π)).choose

lemma spec_levelHom : Spec.map (levelHom π q y) = Y.fromSpecStalk y ≫ q ≫ π :=
  (Spec.map_surjective (Y.fromSpecStalk y ≫ q ≫ π)).choose_spec

instance : Algebra R (LevelRing π q y) := (levelHom π q y).hom.toAlgebra

/-- `Spec 𝒪_{Y,y} ⟶ Y`. -/
def levelJ : Spec (CommRingCat.of (LevelRing π q y)) ⟶ Y := Y.fromSpecStalk y

instance : Mono (levelJ π q y) := inferInstanceAs (Mono (Y.fromSpecStalk y))

lemma levelJ_comp : levelJ π q y ≫ q ≫ π = (ovR R (LevelRing π q y)).hom :=
  (spec_levelHom π q y).symm

variable [Mono π] {F}
variable (e : (baseChange π F).RepresentableBy (Over.mk q))

/-- The element of `F(Spec 𝒪_{Y,y})` given by `Spec 𝒪_{Y,y} ⟶ Y`. -/
def levelElem : F.obj (op (ovR R (LevelRing π q y))) :=
  elemEquiv π e (ovR R (LevelRing π q y)) (levelJ π q y ≫ q)
    (by rw [Category.assoc, levelJ_comp]) (Over.homMk (levelJ π q y) rfl)

/-- The classifying morphism of the restriction of `levelElem` along an `R`-algebra map
`ψ : 𝒪_{Y,y} → A` is `Spec ψ ≫ (Spec 𝒪_{Y,y} ⟶ Y)`. -/
lemma map_levelElem {A : Type u} [CommRing A] [Algebra R A] (t : Spec (CommRingCat.of A) ⟶ T₀)
    (ht : t ≫ π = (ovR R A).hom) (ψ : LevelRing π q y →ₐ[R] A) :
    F.map (homR ψ).op (levelElem π q y e) =
      elemEquiv π e (ovR R A) t ht (Over.homMk (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
        levelJ π q y) (by
          rw [← cancel_mono π]
          change Spec.map _ ≫ levelJ π q y ≫ q ≫ π = t ≫ π
          rw [levelJ_comp, ht]
          exact Over.w (homR ψ))) := by
  rw [levelElem, elemEquiv_naturality π e (homR ψ) t (levelJ π q y ≫ q) ht]
  congr 1

/-- Elements of `F` over a local `R`-algebra lying over `T₀`, whose classifying morphism sends
the closed point to a generization of `y`, come from `levelElem`. -/
lemma exists_levelElem {A : Type u} [CommRing A] [IsLocalRing A] [Algebra R A]
    (t : Spec (CommRingCat.of A) ⟶ T₀) (ht : t ≫ π = (ovR R A).hom)
    (η : F.obj (op (ovR R A)))
    (hη : ((elemEquiv π e (ovR R A) t ht).symm η).left (closedPoint A) ⤳ y) :
    ∃ ψ : LevelRing π q y →ₐ[R] A, F.map (homR ψ).op (levelElem π q y e) = η := by
  set g := (elemEquiv π e (ovR R A) t ht).symm η
  obtain ⟨f', hf'⟩ := exists_comp_fromSpecStalk y g.left hη
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f'
  have hcomm : levelHom π q y ≫ φ = CommRingCat.ofHom (algebraMap R A) := by
    apply Spec.map_injective
    rw [Spec.map_comp, spec_levelHom, ← Category.assoc, ← Category.assoc, hf']
    change g.left ≫ q ≫ π = (ovR R A).hom
    rw [← Category.assoc, show g.left ≫ q = t from Over.w g]
    exact ht
  let ψ : LevelRing π q y →ₐ[R] A :=
    { φ.hom with commutes' := fun r ↦ congrArg (fun f ↦ f.hom r) hcomm }
  refine ⟨ψ, ?_⟩
  rw [map_levelElem π q y e t ht ψ, ← Equiv.eq_symm_apply]
  ext1
  exact hf'

/-- Two `R`-algebra maps out of `𝒪_{Y,y}` to an `R`-algebra lying over `T₀` restricting
`levelElem` to the same element are equal. -/
lemma levelElem_injective {A : Type u} [CommRing A] [Algebra R A]
    (t : Spec (CommRingCat.of A) ⟶ T₀) (ht : t ≫ π = (ovR R A).hom)
    {ψ₁ ψ₂ : LevelRing π q y →ₐ[R] A}
    (h : F.map (homR ψ₁).op (levelElem π q y e) = F.map (homR ψ₂).op (levelElem π q y e)) :
    ψ₁ = ψ₂ := by
  rw [map_levelElem π q y e t ht, map_levelElem π q y e t ht] at h
  have h' := congrArg CommaMorphism.left ((elemEquiv π e (ovR R A) t ht).injective h)
  simp only [Over.homMk_left] at h'
  have := Spec.map_injective ((cancel_mono (levelJ π q y)).1 h')
  ext x
  exact congrArg (fun f ↦ f.hom x) this

section Props

omit [Mono π] in
lemma levelHom_eq : levelHom π q y =
    StructureSheaf.toStalk R ((q ≫ π) y) ≫ (q ≫ π).stalkMap y := by
  apply Spec.map_injective
  rw [spec_levelHom]
  have h := Scheme.SpecMap_stalkMap_fromSpecStalk (q ≫ π) (x := y)
  rw [Spec.fromSpecStalk_eq'] at h
  rw [← h]
  exact (Spec.map_comp _ _).symm

omit [Mono π] in
lemma formallyUnramified_level [FormallyUnramified q] [FormallyUnramified π] :
    Algebra.FormallyUnramified R (LevelRing π q y) := by
  have h1 : FormallyUnramified (Y.fromSpecStalk y) := inferInstance
  have : FormallyUnramified (Spec.map (levelHom π q y)) := by
    rw [spec_levelHom]
    exact MorphismProperty.comp_mem _ _ _ h1
      (MorphismProperty.comp_mem _ _ _ inferInstance inferInstance)
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)] at this
  exact this

omit [Mono π] in
lemma essFiniteType_level [LocallyOfFiniteType q] [LocallyOfFiniteType π] :
    Algebra.EssFiniteType R (LevelRing π q y) := by
  have h1 : (StructureSheaf.toStalk R ((q ≫ π) y)).hom.EssFiniteType := by
    let : Algebra R ((structurePresheafInCommRingCat R).stalk ((q ≫ π) y)) :=
      (StructureSheaf.toStalk R ((q ≫ π) y)).hom.toAlgebra
    have := ((q ≫ π) y).isPrime
    have : IsLocalization.AtPrime ((structurePresheafInCommRingCat R).stalk ((q ≫ π) y))
        ((q ≫ π) y).asIdeal := StructureSheaf.IsLocalization.to_stalk R ((q ≫ π) y)
    exact Algebra.EssFiniteType.of_isLocalization _ ((q ≫ π) y).asIdeal.primeCompl
  have h2 := LocallyOfFiniteType.stalkMap (q ≫ π) y
  have h := h1.comp h2
  show (levelHom π q y).hom.EssFiniteType
  rw [levelHom_eq]
  exact h

end Props

end Level

section Change

variable {F}

/-- Naturality of `elemEquiv`, with the compatibility of the factorizations as a hypothesis
(instead of `Mono g`). -/
lemma elemEquiv_naturality' {S' : Scheme.{u}} (g : S' ⟶ Spec R) {Y' : Over S'}
    (e : (baseChange g F).RepresentableBy Y') {T₁ T₂ : Over (Spec R)} (h : T₁ ⟶ T₂)
    (t₁ : T₁.left ⟶ S') (t₂ : T₂.left ⟶ S') (ht₁ : t₁ ≫ g = T₁.hom) (ht₂ : t₂ ≫ g = T₂.hom)
    (hc : h.left ≫ t₂ = t₁) (a : Over.mk t₂ ⟶ Y') :
    F.map h.op (elemEquiv g e T₂ t₂ ht₂ a) =
      elemEquiv g e T₁ t₁ ht₁ ((Over.homMk h.left hc : Over.mk t₁ ⟶ Over.mk t₂) ≫ a) := by
  have hcomm : h ≫ (liftIso g T₂ t₂ ht₂).hom = (liftIso g T₁ t₁ ht₁).hom ≫
      (Over.map g).map (Over.homMk h.left hc : Over.mk t₁ ⟶ Over.mk t₂) := by
    ext1
    simp [liftIso]
  rw [elemEquiv_apply, elemEquiv_apply, e.homEquiv_comp]
  change (F.map (liftIso g T₂ t₂ ht₂).hom.op ≫ F.map h.op) (e.homEquiv a) =
    (F.map ((Over.map g).map (Over.homMk h.left hc : Over.mk t₁ ⟶ Over.mk t₂)).op ≫
      F.map (liftIso g T₁ t₁ ht₁).hom.op) (e.homEquiv a)
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, hcomm]

section Cls

variable {S' : Scheme.{u}} (g : S' ⟶ Spec R) {Y : Scheme.{u}} {q : Y ⟶ S'}
  (e : (baseChange g F).RepresentableBy (Over.mk q))

/-- The classifying morphism `T.left ⟶ Y` of an element of `F(T)`, for `T` lying over `S'`
through `t`. -/
def cls (T : Over (Spec R)) (t : T.left ⟶ S') (ht : t ≫ g = T.hom) (x : F.obj (op T)) :
    T.left ⟶ Y :=
  ((elemEquiv g e T t ht).symm x).left

lemma cls_w (T : Over (Spec R)) (t : T.left ⟶ S') (ht : t ≫ g = T.hom) (x : F.obj (op T)) :
    cls g e T t ht x ≫ q = t :=
  Over.w ((elemEquiv g e T t ht).symm x)

/-- The element of `F(T)` given by a morphism `f : T.left ⟶ Y` over `S'`. -/
def mkElem (T : Over (Spec R)) (t : T.left ⟶ S') (ht : t ≫ g = T.hom) (f : T.left ⟶ Y)
    (hf : f ≫ q = t) : F.obj (op T) :=
  elemEquiv g e T t ht (Over.homMk f hf)

@[simp]
lemma cls_mkElem (T : Over (Spec R)) (t : T.left ⟶ S') (ht : t ≫ g = T.hom) (f : T.left ⟶ Y)
    (hf : f ≫ q = t) : cls g e T t ht (mkElem g e T t ht f hf) = f := by
  simp [cls, mkElem]

lemma mkElem_cls (T : Over (Spec R)) (t : T.left ⟶ S') (ht : t ≫ g = T.hom)
    (x : F.obj (op T)) : mkElem g e T t ht (cls g e T t ht x) (cls_w g e T t ht x) = x := by
  rw [mkElem, ← Equiv.eq_symm_apply]
  rfl

lemma eq_of_cls_eq (T : Over (Spec R)) (t : T.left ⟶ S') (ht : t ≫ g = T.hom)
    {x y : F.obj (op T)} (h : cls g e T t ht x = cls g e T t ht y) : x = y := by
  rw [← mkElem_cls g e T t ht x, ← mkElem_cls g e T t ht y]
  congr 1

lemma cls_congr {T : Over (Spec R)} {t t' : T.left ⟶ S'} (h : t = t') (ht : t ≫ g = T.hom)
    (ht' : t' ≫ g = T.hom) (x : F.obj (op T)) : cls g e T t ht x = cls g e T t' ht' x := by
  subst h; rfl

/-- Restriction of `mkElem` along a morphism of `Over (Spec R)`. -/
lemma map_mkElem {T₁ T₂ : Over (Spec R)} (h : T₁ ⟶ T₂) (t₁ : T₁.left ⟶ S') (t₂ : T₂.left ⟶ S')
    (ht₁ : t₁ ≫ g = T₁.hom) (ht₂ : t₂ ≫ g = T₂.hom) (hc : h.left ≫ t₂ = t₁) (f : T₂.left ⟶ Y)
    (hf : f ≫ q = t₂) :
    F.map h.op (mkElem g e T₂ t₂ ht₂ f hf) =
      mkElem g e T₁ t₁ ht₁ (h.left ≫ f) (by rw [Category.assoc, hf, hc]) := by
  rw [mkElem, elemEquiv_naturality' g e h t₁ t₂ ht₁ ht₂ hc]
  rfl

lemma cls_map {T₁ T₂ : Over (Spec R)} (h : T₁ ⟶ T₂) (t₁ : T₁.left ⟶ S') (t₂ : T₂.left ⟶ S')
    (ht₁ : t₁ ≫ g = T₁.hom) (ht₂ : t₂ ≫ g = T₂.hom) (hc : h.left ≫ t₂ = t₁)
    (x : F.obj (op T₂)) : cls g e T₁ t₁ ht₁ (F.map h.op x) = h.left ≫ cls g e T₂ t₂ ht₂ x := by
  rw [← mkElem_cls g e T₂ t₂ ht₂ x, map_mkElem g e h t₁ t₂ ht₁ ht₂ hc, cls_mkElem, cls_mkElem]

/-- The universal element of `F(Y)`. -/
def univ : F.obj (op (Over.mk (q ≫ g))) :=
  mkElem g e (Over.mk (q ≫ g)) q rfl (𝟙 Y) (Category.id_comp q)

/-- A morphism `f : T.left ⟶ Y` over `S'` as a morphism `T ⟶ Y` of `Over (Spec R)`. -/
def univHom {T : Over (Spec R)} {t : T.left ⟶ S'} (ht : t ≫ g = T.hom) (f : T.left ⟶ Y)
    (hf : f ≫ q = t) : T ⟶ Over.mk (q ≫ g) :=
  Over.homMk f (by change f ≫ q ≫ g = T.hom; rw [← Category.assoc, hf, ht])

/-- Every element of `F(T)` lying over `S'` is a restriction of the universal element. -/
lemma eq_map_univ (T : Over (Spec R)) (t : T.left ⟶ S') (ht : t ≫ g = T.hom)
    (x : F.obj (op T)) :
    x = F.map (univHom g ht (cls g e T t ht x) (cls_w g e T t ht x)).op (univ g e) := by
  rw [univ, map_mkElem g e (univHom g ht (cls g e T t ht x) (cls_w g e T t ht x)) t q ht rfl
    (cls_w g e T t ht x) (𝟙 Y) (Category.id_comp q)]
  conv_lhs => rw [← mkElem_cls g e T t ht x]
  congr 1

end Cls

variable {T₁ T₂ : Scheme.{u}} (π₁ : T₁ ⟶ Spec R) (π₂ : T₂ ⟶ Spec R)
  {ι : T₁ ⟶ T₂} (hι : ι ≫ π₂ = π₁) {Y₁ Y₂ : Scheme.{u}} {q₁ : Y₁ ⟶ T₁} {q₂ : Y₂ ⟶ T₂}
  (e₁ : (baseChange π₁ F).RepresentableBy (Over.mk q₁))
  (e₂ : (baseChange π₂ F).RepresentableBy (Over.mk q₂))

include hι in
lemma change_fac {T : Over (Spec R)} (t : T.left ⟶ T₁) (ht : t ≫ π₁ = T.hom) :
    (t ≫ ι) ≫ π₂ = T.hom := by
  rw [Category.assoc, hι, ht]

/-- The morphism `Y₁ ⟶ Y₂` classifying the universal element of `F(Y₁)` over `T₂`. -/
def changeMap : Y₁ ⟶ Y₂ :=
  cls π₂ e₂ (Over.mk (q₁ ≫ π₁)) (q₁ ≫ ι) (change_fac π₁ π₂ hι (T := Over.mk (q₁ ≫ π₁)) q₁ rfl)
    (univ π₁ e₁)

lemma changeMap_w : changeMap π₁ π₂ hι e₁ e₂ ≫ q₂ = q₁ ≫ ι :=
  cls_w _ _ _ _ _ _

/-- The classifying morphism over `T₂` of an element lying over `T₁` is its classifying
morphism over `T₁` followed by `changeMap`. -/
lemma cls_changeMap {T : Over (Spec R)} (t : T.left ⟶ T₁) (ht : t ≫ π₁ = T.hom)
    (x : F.obj (op T)) :
    cls π₂ e₂ T (t ≫ ι) (change_fac π₁ π₂ hι t ht) x =
      cls π₁ e₁ T t ht x ≫ changeMap π₁ π₂ hι e₁ e₂ := by
  have key := cls_map π₂ e₂ (univHom π₁ ht (cls π₁ e₁ T t ht x) (cls_w π₁ e₁ T t ht x))
    (t ≫ ι) (q₁ ≫ ι) (change_fac π₁ π₂ hι t ht)
    (change_fac π₁ π₂ hι (T := Over.mk (q₁ ≫ π₁)) q₁ rfl)
    (by change cls π₁ e₁ T t ht x ≫ q₁ ≫ ι = t ≫ ι; rw [← Category.assoc, cls_w])
    (univ π₁ e₁)
  rw [← eq_map_univ π₁ e₁ T t ht x] at key
  exact key

end Change

section Tower

variable [IsLocalRing R]

/-- The closed immersion `Spec (R/m^(k+1)) ⟶ Spec (R/m^(l+1))` for `k ≤ l`. -/
def levelMap {k l : ℕ} (hkl : k ≤ l) :
    Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (k + 1))) ⟶
      Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (l + 1))) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.succ_le_succ hkl))))

lemma levelMap_comp {k l : ℕ} (hkl : k ≤ l) :
    levelMap (R := R) hkl ≫ maximalIdealPowQuotientMap R l = maximalIdealPowQuotientMap R k := by
  rw [levelMap, maximalIdealPowQuotientMap, maximalIdealPowQuotientMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rfl

lemma levelMap_trans {k l n : ℕ} (hkl : k ≤ l) (hln : l ≤ n) :
    levelMap (R := R) hkl ≫ levelMap hln = levelMap (hkl.trans hln) := by
  rw [levelMap, levelMap, levelMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  rfl

instance monoQuot (k : ℕ) : Mono (maximalIdealPowQuotientMap R k) := by
  have : IsClosedImmersion (maximalIdealPowQuotientMap R k) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

instance {k l : ℕ} (hkl : k ≤ l) : Mono (levelMap (R := R) hkl) := by
  have : IsClosedImmersion (levelMap (R := R) hkl) :=
    IsClosedImmersion.spec_of_surjective _
      (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.succ_le_succ hkl)))
  infer_instance

variable {F} {Y : ℕ → Scheme.{u}}
  {q : ∀ k, Y k ⟶ Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (k + 1)))}
  (e : ∀ k, (baseChange (maximalIdealPowQuotientMap R k) F).RepresentableBy (Over.mk (q k)))

/-- The morphism `Y k ⟶ Y l` classifying the universal element of level `k` at level `l`. -/
def towerMap {k l : ℕ} (hkl : k ≤ l) : Y k ⟶ Y l :=
  changeMap _ _ (levelMap_comp (R := R) hkl) (e k) (e l)

lemma towerMap_w {k l : ℕ} (hkl : k ≤ l) :
    towerMap e hkl ≫ q l = q k ≫ levelMap (R := R) hkl :=
  changeMap_w _ _ _ _ _

lemma cls_towerMap {k l : ℕ} (hkl : k ≤ l) {T : Over (Spec R)}
    (t : T.left ⟶ Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (k + 1))))
    (ht : t ≫ maximalIdealPowQuotientMap R k = T.hom) (x : F.obj (op T)) :
    cls _ (e l) T (t ≫ levelMap (R := R) hkl) (change_fac _ _ (levelMap_comp (R := R) hkl) t ht)
      x = cls _ (e k) T t ht x ≫ towerMap e hkl :=
  cls_changeMap _ _ (levelMap_comp (R := R) hkl) (e k) (e l) t ht x

lemma towerMap_comp {k l n : ℕ} (hkl : k ≤ l) (hln : l ≤ n) :
    towerMap e hkl ≫ towerMap e hln = towerMap e (hkl.trans hln) := by
  have h1 := cls_towerMap e hln (T := Over.mk (q k ≫ maximalIdealPowQuotientMap R k))
    (q k ≫ levelMap (R := R) hkl)
    (change_fac _ _ (levelMap_comp (R := R) hkl) (T := Over.mk (q k ≫ maximalIdealPowQuotientMap R k)) (q k) rfl)
    (univ _ (e k))
  rw [cls_congr _ (e n) (by rw [Category.assoc, levelMap_trans]) _
    (change_fac _ _ (levelMap_comp (R := R) (hkl.trans hln))
      (T := Over.mk (q k ≫ maximalIdealPowQuotientMap R k)) (q k) rfl)] at h1
  exact h1.symm

instance towerMap_mono {k l : ℕ} (hkl : k ≤ l) : Mono (towerMap e hkl) := by
  constructor
  intro W a b hab
  have hq : a ≫ q k = b ≫ q k := by
    rw [← cancel_mono (levelMap (R := R) hkl), Category.assoc, Category.assoc,
      ← towerMap_w e hkl, ← Category.assoc, hab, Category.assoc]
  let T : Over (Spec R) := Over.mk (a ≫ q k ≫ maximalIdealPowQuotientMap R k)
  have ht : (a ≫ q k) ≫ maximalIdealPowQuotientMap R k = T.hom := Category.assoc _ _ _
  have h1 := cls_towerMap e hkl (T := T) (a ≫ q k) ht (mkElem _ (e k) T (a ≫ q k) ht a rfl)
  have h2 := cls_towerMap e hkl (T := T) (a ≫ q k) ht (mkElem _ (e k) T (a ≫ q k) ht b hq.symm)
  rw [cls_mkElem] at h1 h2
  have h3 := eq_of_cls_eq _ (e l) T _ _ (h1.trans (hab.trans h2.symm))
  have h4 := congrArg (cls _ (e k) T (a ≫ q k) ht) h3
  rwa [cls_mkElem, cls_mkElem] at h4

lemma levelMap_refl' (k : ℕ) (h : k ≤ k) : levelMap (R := R) h = 𝟙 _ := by
  rw [levelMap, ← Spec.map_id]
  congr 1
  ext x
  rfl

lemma towerMap_refl (k : ℕ) (h : k ≤ k) : towerMap e h = 𝟙 (Y k) := by
  change cls _ (e k) (Over.mk (q k ≫ maximalIdealPowQuotientMap R k)) (q k ≫ levelMap h) _
    (univ _ (e k)) = _
  rw [cls_congr _ (e k) (by rw [levelMap_refl', Category.comp_id]) _ rfl, univ, cls_mkElem]

/-- The point of `Y k` corresponding to a point `y` of `Y 0`. -/
def pt (y : Y 0) (k : ℕ) : Y k := towerMap e (Nat.zero_le k) y

lemma towerMap_pt (y : Y 0) {k l : ℕ} (hkl : k ≤ l) : towerMap e hkl (pt e y k) = pt e y l := by
  rw [pt, pt, ← Scheme.Hom.comp_apply, towerMap_comp]

lemma pt_zero (y : Y 0) : pt e y 0 = y := by
  rw [pt, towerMap_refl]
  rfl

/-- The stalk of `Y k` at the point corresponding to `y`. -/
abbrev Bk (y : Y 0) (k : ℕ) : Type u :=
  LevelRing (maximalIdealPowQuotientMap R k) (q k) (pt e y k)

/-- The element of `F(Spec (Bk y k))` given by `Spec (Bk y k) ⟶ Y k`. -/
def ξk (y : Y 0) (k : ℕ) : F.obj (op (ovR R (Bk e y k))) :=
  levelElem _ (q k) (pt e y k) (e k)

lemma ξk_fac (y : Y 0) (k : ℕ) :
    (levelJ _ (q k) (pt e y k) ≫ q k) ≫ maximalIdealPowQuotientMap R k = (ovR R (Bk e y k)).hom := by
  rw [Category.assoc, levelJ_comp]

lemma cls_ξk (y : Y 0) (k : ℕ) :
    cls _ (e k) (ovR R (Bk e y k)) (levelJ _ (q k) (pt e y k) ≫ q k) (ξk_fac e y k) (ξk e y k) =
      levelJ _ (q k) (pt e y k) :=
  cls_mkElem _ (e k) _ _ _ _ rfl

lemma transition_fac (y : Y 0) (k : ℕ) :
    ((levelJ _ (q k) (pt e y k) ≫ q k) ≫ levelMap (R := R) (Nat.le_succ k)) ≫
      maximalIdealPowQuotientMap R (k + 1) = (ovR R (Bk e y k)).hom := by
  rw [Category.assoc, levelMap_comp, ξk_fac]

lemma exists_transition (y : Y 0) (k : ℕ) :
    ∃ ψ : Bk e y (k + 1) →ₐ[R] Bk e y k, F.map (homR ψ).op (ξk e y (k + 1)) = ξk e y k := by
  apply exists_levelElem _ (q (k + 1)) (pt e y (k + 1)) (e (k + 1)) _ (transition_fac e y k)
  apply Specializes.of_eq
  change cls _ (e (k + 1)) _ _ _ (ξk e y k) (closedPoint _) = _
  rw [cls_towerMap e (Nat.le_succ k) (T := ovR R (Bk e y k)) (levelJ _ (q k) (pt e y k) ≫ q k)
    (ξk_fac e y k), cls_ξk]
  show towerMap e (Nat.le_succ k) ((Y k).fromSpecStalk (pt e y k) (closedPoint _)) = _
  rw [Scheme.fromSpecStalk_closedPoint, towerMap_pt]

/-- The transition map `Bk y (k+1) → Bk y k`. -/
def transition (y : Y 0) (k : ℕ) : Bk e y (k + 1) →ₐ[R] Bk e y k :=
  (exists_transition e y k).choose

lemma map_transition (y : Y 0) (k : ℕ) :
    F.map (homR (transition e y k)).op (ξk e y (k + 1)) = ξk e y k :=
  (exists_transition e y k).choose_spec

omit [IsLocalRing R] in
/-- A ring map whose spectrum factors through `Spec (R/I)` kills `I`. -/
lemma eq_zero_of_spec_fac {A : CommRingCat.{u}} (I : Ideal R) (f : R ⟶ A)
    (g : Spec A ⟶ Spec (CommRingCat.of (R ⧸ I)))
    (h : Spec.map f = g ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) {r : R}
    (hr : r ∈ I) : f.hom r = 0 := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp] at h
  rw [Spec.map_injective h]
  change φ.hom (Ideal.Quotient.mk I r) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]

lemma algebraMap_Bk_eq_zero (y : Y 0) (k : ℕ) {r : R} (hr : r ∈ maximalIdeal R ^ (k + 1)) :
    algebraMap R (Bk e y k) r = 0 :=
  eq_zero_of_spec_fac _ (levelHom _ (q k) (pt e y k)) (levelJ (maximalIdealPowQuotientMap R k) (q k) (pt e y k) ≫ q k)
    ((spec_levelHom _ (q k) (pt e y k)).trans (Category.assoc _ _ _).symm) hr

/-- The ideal `m^(k+1) · Bk y (k+1)`. -/
abbrev transIdeal (y : Y 0) (k : ℕ) : Ideal (Bk e y (k + 1)) :=
  (maximalIdeal R ^ (k + 1)).map (algebraMap R (Bk e y (k + 1)))

lemma transIdeal_le (y : Y 0) (k : ℕ) : transIdeal e y k ≤ RingHom.ker (transition e y k) := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes]
  exact algebraMap_Bk_eq_zero e y k hr

lemma transIdeal_ne_top (y : Y 0) (k : ℕ) : transIdeal e y k ≠ ⊤ := by
  intro h
  have := transIdeal_le e y k (h ▸ Submodule.mem_top : (1 : Bk e y (k + 1)) ∈ transIdeal e y k)
  rw [RingHom.mem_ker, map_one] at this
  exact one_ne_zero this

/-- The quotient `Bk y (k+1) / m^(k+1)`. -/
abbrev TransQ (y : Y 0) (k : ℕ) : Type u := Bk e y (k + 1) ⧸ transIdeal e y k

instance (y : Y 0) (k : ℕ) : Nontrivial (TransQ e y k) :=
  Ideal.Quotient.nontrivial_iff.2 (transIdeal_ne_top e y k)

instance (y : Y 0) (k : ℕ) : IsLocalRing (TransQ e y k) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- The quotient map `Bk y (k+1) → TransQ y k`. -/
abbrev transMk (y : Y 0) (k : ℕ) : Bk e y (k + 1) →ₐ[R] TransQ e y k :=
  Ideal.Quotient.mkₐ R (transIdeal e y k)

/-- `R/m^(k+1) → TransQ y k`. -/
def transQLift (y : Y 0) (k : ℕ) :
    CommRingCat.of (R ⧸ maximalIdeal R ^ (k + 1)) ⟶ CommRingCat.of (TransQ e y k) :=
  CommRingCat.ofHom (Ideal.Quotient.lift _ (algebraMap R (TransQ e y k)) (fun r hr ↦ by
    rw [IsScalarTower.algebraMap_apply R (Bk e y (k + 1)) (TransQ e y k),
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hr))

lemma transQ_fac (y : Y 0) (k : ℕ) :
    Spec.map (transQLift e y k) ≫ maximalIdealPowQuotientMap R k = (ovR R (TransQ e y k)).hom := by
  show Spec.map (transQLift e y k) ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (k + 1)))) = _
  rw [← Spec.map_comp]
  congr 1

/-- The restriction of `ξk y (k+1)` to `TransQ y k`. -/
def ηQ (y : Y 0) (k : ℕ) : F.obj (op (ovR R (TransQ e y k))) :=
  F.map (homR (transMk e y k)).op (ξk e y (k + 1))

lemma cls_ηQ_closedPoint (y : Y 0) (k : ℕ) :
    cls _ (e k) (ovR R (TransQ e y k)) (Spec.map (transQLift e y k)) (transQ_fac e y k)
      (ηQ e y k) (closedPoint _) = pt e y k := by
  have h1 := cls_towerMap e (Nat.le_succ k) (T := ovR R (TransQ e y k))
    (Spec.map (transQLift e y k)) (transQ_fac e y k) (ηQ e y k)
  have ht' : (Spec.map (CommRingCat.ofHom (transMk e y k).toRingHom) ≫
      levelJ (maximalIdealPowQuotientMap R (k + 1)) (q (k + 1)) (pt e y (k + 1)) ≫ q (k + 1)) ≫
        maximalIdealPowQuotientMap R (k + 1) = (ovR R (TransQ e y k)).hom := by
    rw [Category.assoc, ξk_fac e y (k + 1)]
    exact Over.w (homR (transMk e y k))
  have heq : Spec.map (transQLift e y k) ≫ levelMap (R := R) (Nat.le_succ k) =
      Spec.map (CommRingCat.ofHom (transMk e y k).toRingHom) ≫
        levelJ (maximalIdealPowQuotientMap R (k + 1)) (q (k + 1)) (pt e y (k + 1)) ≫ q (k + 1) := by
    rw [← cancel_mono (maximalIdealPowQuotientMap R (k + 1)), ht', Category.assoc,
      levelMap_comp, transQ_fac]
  have h2 := cls_map _ (e (k + 1)) (homR (transMk e y k))
    (Spec.map (CommRingCat.ofHom (transMk e y k).toRingHom) ≫
      levelJ (maximalIdealPowQuotientMap R (k + 1)) (q (k + 1)) (pt e y (k + 1)) ≫ q (k + 1))
    (levelJ (maximalIdealPowQuotientMap R (k + 1)) (q (k + 1)) (pt e y (k + 1)) ≫ q (k + 1)) ht' (ξk_fac e y (k + 1)) rfl
    (ξk e y (k + 1))
  rw [cls_ξk] at h2
  rw [cls_congr _ (e (k + 1)) heq _ ht'] at h1
  have h3 := congrArg (fun f ↦ f (closedPoint (TransQ e y k))) (h1.symm.trans h2)
  have : IsLocalHom (CommRingCat.ofHom (transMk e y k).toRingHom).hom :=
    isLocalHom_of_le_jacobson_bot _ (by
      rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      exact IsLocalRing.le_maximalIdeal (transIdeal_ne_top e y k))
  change towerMap e (Nat.le_succ k) (cls _ (e k) (ovR R (TransQ e y k))
      (Spec.map (transQLift e y k)) (transQ_fac e y k) (ηQ e y k) (closedPoint _)) =
    (Y (k + 1)).fromSpecStalk (pt e y (k + 1))
      (Spec.map (CommRingCat.ofHom (transMk e y k).toRingHom) (closedPoint _)) at h3
  have h4 : (Y (k + 1)).fromSpecStalk (pt e y (k + 1)) (closedPoint (Bk e y (k + 1))) =
      pt e y (k + 1) := Scheme.fromSpecStalk_closedPoint
  rw [Spec_closedPoint, h4] at h3
  exact (towerMap e (Nat.le_succ k)).injective (h3.trans (towerMap_pt e y (Nat.le_succ k)).symm)

lemma exists_transInv (y : Y 0) (k : ℕ) :
    ∃ σ : Bk e y k →ₐ[R] TransQ e y k, F.map (homR σ).op (ξk e y k) = ηQ e y k :=
  exists_levelElem _ (q k) (pt e y k) (e k) (Spec.map (transQLift e y k)) (transQ_fac e y k)
    (ηQ e y k) (Specializes.of_eq (cls_ηQ_closedPoint e y k))

/-- The map `TransQ y k → Bk y k` induced by `transition`. -/
def transBar (y : Y 0) (k : ℕ) : TransQ e y k →ₐ[R] Bk e y k :=
  Ideal.Quotient.liftₐ (transIdeal e y k) (transition e y k)
    (fun _ hb ↦ (RingHom.mem_ker).1 (transIdeal_le e y k hb))

lemma transBar_comp_transInv (y : Y 0) (k : ℕ) :
    (transBar e y k).comp (exists_transInv e y k).choose = AlgHom.id R (Bk e y k) := by
  set σ := (exists_transInv e y k).choose
  have hσ : F.map (homR σ).op (ξk e y k) = ηQ e y k := (exists_transInv e y k).choose_spec
  apply levelElem_injective _ (q k) (pt e y k) (e k)
    (levelJ (maximalIdealPowQuotientMap R k) (q k) (pt e y k) ≫ q k) (ξk_fac e y k)
  change F.map (homR _).op (ξk e y k) = F.map (homR _).op (ξk e y k)
  rw [← map_homR_map_homR, hσ, ηQ, map_homR_map_homR, transBar, Ideal.Quotient.liftₐ_comp,
    map_transition, ArtinianBase.homR_id, op_id, F.map_id]
  rfl

lemma transInv_comp_transBar (y : Y 0) (k : ℕ) :
    (exists_transInv e y k).choose.comp (transBar e y k) = AlgHom.id R (TransQ e y k) := by
  set σ := (exists_transInv e y k).choose
  have hσ : F.map (homR σ).op (ξk e y k) = ηQ e y k := (exists_transInv e y k).choose_spec
  apply Ideal.Quotient.algHom_ext
  apply levelElem_injective _ (q (k + 1)) (pt e y (k + 1)) (e (k + 1))
    (Spec.map (transQLift e y k) ≫ levelMap (R := R) (Nat.le_succ k))
    (change_fac _ _ (levelMap_comp (R := R) (Nat.le_succ k)) (T := ovR R (TransQ e y k))
      (Spec.map (transQLift e y k)) (transQ_fac e y k))
  change F.map (homR _).op (ξk e y (k + 1)) = F.map (homR _).op (ξk e y (k + 1))
  rw [AlgHom.comp_assoc, ← map_homR_map_homR, transBar, Ideal.Quotient.liftₐ_comp,
    map_transition, hσ, AlgHom.id_comp]
  rfl

lemma transition_surjective (y : Y 0) (k : ℕ) : Function.Surjective (transition e y k) := by
  intro b
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((exists_transInv e y k).choose b)
  refine ⟨a, ?_⟩
  have h := congrArg (fun f : Bk e y k →ₐ[R] Bk e y k ↦ f b) (transBar_comp_transInv e y k)
  simp only [AlgHom.comp_apply, AlgHom.id_apply] at h
  rw [← ha] at h
  exact h

lemma transition_ker (y : Y 0) (k : ℕ) :
    RingHom.ker (transition e y k) = transIdeal e y k := by
  refine le_antisymm (fun x hx ↦ ?_) (transIdeal_le e y k)
  rw [RingHom.mem_ker] at hx
  have h := congrArg (fun f : TransQ e y k →ₐ[R] TransQ e y k ↦ f (Ideal.Quotient.mk _ x))
    (transInv_comp_transBar e y k)
  simp only [AlgHom.comp_apply, AlgHom.id_apply] at h
  change (exists_transInv e y k).choose (transition e y k x) = _ at h
  rw [hx, map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at h
  exact h

lemma transition_ker_linear (y : Y 0) (k : ℕ) :
    LinearMap.ker (transition e y k).toLinearMap =
      (maximalIdeal R) ^ (k + 1) • (⊤ : Submodule R (Bk e y (k + 1))) := by
  ext x
  rw [LinearMap.mem_ker, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
  change transition e y k x = 0 ↔ _
  rw [← RingHom.mem_ker, transition_ker]

instance (k : ℕ) : FormallyUnramified (maximalIdealPowQuotientMap R k) := inferInstance

instance (k : ℕ) : LocallyOfFiniteType (maximalIdealPowQuotientMap R k) := by
  have : IsClosedImmersion (maximalIdealPowQuotientMap R k) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

section Zero

variable (hfu : ∀ k, FormallyUnramified (q k)) (hlft : ∀ k, LocallyOfFiniteType (q k))
include hfu hlft

omit hlft in
lemma Bk_formallyUnramified (y : Y 0) (k : ℕ) : Algebra.FormallyUnramified R (Bk e y k) := by
  have := hfu k
  exact formallyUnramified_level _ _ _

omit hfu in
lemma Bk_essFiniteType (y : Y 0) (k : ℕ) : Algebra.EssFiniteType R (Bk e y k) := by
  have := hlft k
  exact essFiniteType_level _ _ _

omit hfu hlft in
lemma Bk_isLocalHom (y : Y 0) (k : ℕ) : IsLocalHom (algebraMap R (Bk e y k)) := ⟨fun r hr ↦ by
  by_contra h
  have hm : r ^ (k + 1) ∈ maximalIdeal R ^ (k + 1) :=
    Ideal.pow_mem_pow ((mem_maximalIdeal r).2 h) _
  have h0 := algebraMap_Bk_eq_zero e y k hm
  rw [map_pow] at h0
  exact not_isUnit_zero (h0 ▸ hr.pow (k + 1))⟩

lemma B0_isField (y : Y 0) : IsField (Bk e y 0) := by
  have := Bk_formallyUnramified e hfu y 0
  have := Bk_essFiniteType e hlft y 0
  have := Bk_isLocalHom e y 0
  have hmax := Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := Bk e y 0)
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← hmax, Ideal.map_eq_bot_iff_le_ker]
  intro r hr
  rw [RingHom.mem_ker]
  exact algebraMap_Bk_eq_zero e y 0 (by rw [zero_add, pow_one]; exact hr)

lemma B0_finite (y : Y 0) : Module.Finite R (Bk e y 0) := by
  have := Bk_formallyUnramified e hfu y 0
  have := Bk_essFiniteType e hlft y 0
  have := Bk_isLocalHom e y 0
  have hf := B0_isField e hfu hlft y
  have : Module.Finite R (ResidueField R) :=
    inferInstanceAs (Module.Finite R (R ⧸ maximalIdeal R))
  have : Module.Finite R (ResidueField (Bk e y 0)) :=
    Module.Finite.trans (ResidueField R) (ResidueField (Bk e y 0))
  let φ := IsScalarTower.toAlgHom R (Bk e y 0) (ResidueField (Bk e y 0))
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have : x ∈ maximalIdeal (Bk e y 0) := (residue_eq_zero_iff x).1 hx
    rwa [(IsLocalRing.isField_iff_maximalIdeal_eq).1 hf, Ideal.mem_bot] at this
  exact Module.Finite.equiv
    (LinearEquiv.ofBijective φ.toLinearMap ⟨hinj, residue_surjective⟩).symm

end Zero

end Tower

end CompleteLocal

end Langlands.AlgebraicGeometry.UnramifiedFunctor
