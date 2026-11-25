/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections

/-! # The constant system of modules on a ringed site

The sectionwise characterizations determine the functor, including its horizontal
maps. In particular its derived functor is an actual functor to the localization
of the abelian category of systems.

## References

* Zheng, Construction 4.1
* Stacks, Tag 0941
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u c v r
open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.SemilinearSections

section Generic

variable {D : Type*} [Category D] {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}

/-- Restriction of scalars along a ring endomorphism equal to the identity is the identity. -/
theorem sheafOfModules_restrictScalars_eq_id (α : S ⟶ S) (hα : α = 𝟙 S) :
    SheafOfModules.restrictScalars.{u} α = 𝟭 _ := by
  subst hα
  rfl

/-- Sheaves of modules with equal underlying presheaves are equal. -/
theorem sheafOfModules_ext {M N : SheafOfModules.{u} S} (h : M.val = N.val) : M = N := by
  obtain ⟨M, _⟩ := M
  obtain ⟨N, _⟩ := N
  subst h
  rfl

/-- Restriction of scalars along a ring endomorphism equal to the identity is the identity
on objects. -/
theorem moduleCat_restrictScalars_obj_eq_self {A : RingCat.{u}} (f : A ⟶ A) (hf : f = 𝟙 A)
    (M : ModuleCat.{u} A) : (ModuleCat.restrictScalars f.hom).obj M = M := by
  subst hf
  rfl

/-- Morphisms of sheaves of modules with heterogeneously equal sections are heterogeneously
equal. -/
theorem sheafOfModules_hom_heq {A A' B B' : SheafOfModules.{u} S} (hA : A = A') (hB : B = B')
    (g : A ⟶ B) (g' : A' ⟶ B')
    (h : ∀ (U : Dᵒᵖ) (x : A.val.obj U) (y : A'.val.obj U), x ≍ y → g.val.app U x ≍ g'.val.app U y) :
    g ≍ g' := by
  subst hA hB
  refine heq_of_eq (SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦ ?_))
  ext x
  exact eq_of_heq (h U x x HEq.rfl)

/-- Restriction of scalars along a ring endomorphism equal to the identity is injective
on objects. -/
theorem moduleCat_restrictScalars_obj_injective {A : RingCat.{u}} (f : A ⟶ A) (hf : f = 𝟙 A)
    {M N : ModuleCat.{u} A}
    (h : (ModuleCat.restrictScalars f.hom).obj M = (ModuleCat.restrictScalars f.hom).obj N) :
    M = N := by
  subst hf
  exact h

/-- Equal sheaves of modules have equal restriction maps, applied to equal sections. -/
theorem sheafOfModules_map_heq {M N : SheafOfModules.{u} S} (h : M = N) {U V : Dᵒᵖ}
    (f : U ⟶ V) (x : M.val.obj U) (y : N.val.obj U) (hxy : x ≍ y) :
    M.val.map f x ≍ N.val.map f y := by
  subst h
  obtain rfl := eq_of_heq hxy
  rfl

/-- Heterogeneously equal morphisms of sheaves of modules have equal sections. -/
theorem sheafOfModules_app_heq {A A' B B' : SheafOfModules.{u} S} (hA : A = A') (hB : B = B')
    (g : A ⟶ B) (g' : A' ⟶ B') (h : g ≍ g') (U : Dᵒᵖ) (x : A.val.obj U) (y : A'.val.obj U)
    (hxy : x ≍ y) : g.val.app U x ≍ g'.val.app U y := by
  subst hA hB
  obtain rfl := eq_of_heq h
  obtain rfl := eq_of_heq hxy
  rfl

/-- A morphism of sheaves of modules all of whose sections are identities is the identity,
up to the identification of its source and target. -/
theorem sheafOfModules_heq_id_of_app {A B M : SheafOfModules.{u} S} (hA : A = M) (hB : B = M)
    (g : A ⟶ B) (hg : ∀ (U : Dᵒᵖ) (x : A.val.obj U), g.val.app U x ≍ x) : g ≍ 𝟙 M := by
  subst hA hB
  refine heq_of_eq (SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦ ?_))
  ext x
  exact eq_of_heq (hg U x)

/-- Two presheaves of modules with the same modules and heterogeneously equal restriction
maps are equal. -/
theorem presheafOfModules_ext {R : Dᵒᵖ ⥤ RingCat.{u}} {M N : PresheafOfModules.{u} R}
    (hobj : M.obj = N.obj)
    (hmap : ∀ {U V : Dᵒᵖ} (f : U ⟶ V) (x : M.obj U) (y : N.obj U), x ≍ y →
      M.map f x ≍ N.map f y) : M = N := by
  obtain ⟨Mo, Mm, _, _⟩ := M
  obtain ⟨No, Nm, _, _⟩ := N
  obtain rfl : Mo = No := hobj
  obtain rfl : @Mm = @Nm := by
    funext U V f
    ext x
    exact eq_of_heq (hmap f x x HEq.rfl)
  rfl

end Generic

section Systems

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- The sections of the transition are the horizontal restriction maps. -/
theorem transition_app_apply (X : Systems.{c, v, r} J B τ) {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ)
    (x : ((evaluation.{c, v, r} J B τ m).obj X).val.obj U) :
    ((transition.{c, v, r} J B τ h).app X).val.app U x =
      X.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x :=
  congrFun (eq_of_heq ((transition_exists.{c, v, r} J B τ h).exists.choose_spec X U)) x

/-- The identification of the evaluated ring is the identity on sections. -/
theorem evaluation_ring_app (n : ℕ) (U : Cᵒᵖ) :
    (eqToHom (evaluation_ring.{c, v, r} J B τ n).symm).hom.app U = 𝟙 _ := by
  rw [ObjectProperty.eqToHom_hom, eqToHom_app]
  rfl

private theorem system_obj_eq_of_evaluation {X Y : Systems.{c, v, r} J B τ}
    (n : ℕ) (he : (evaluation.{c, v, r} J B τ n).obj X =
      (evaluation.{c, v, r} J B τ n).obj Y) (U : Cᵒᵖ) :
    X.val.obj (op (n, U.unop)) = Y.val.obj (op (n, U.unop)) := by
  exact moduleCat_restrictScalars_obj_injective _ (evaluation_ring_app J B τ n U)
    (congrArg (fun Z ↦ Z.val.obj U) he)

private theorem system_vertical_map_heq {X Y : Systems.{c, v, r} J B τ}
    (n : ℕ) (he : (evaluation.{c, v, r} J B τ n).obj X =
      (evaluation.{c, v, r} J B τ n).obj Y) {U V : Cᵒᵖ} (g : U ⟶ V)
    (x : X.val.obj (op (n, U.unop))) (y : Y.val.obj (op (n, U.unop))) (hxy : x ≍ y) :
    X.val.map ((Prod.sectR n C).map g.unop).op x ≍
      Y.val.map ((Prod.sectR n C).map g.unop).op y := by
  exact sheafOfModules_map_heq he g x y hxy

private theorem system_horizontal_map_heq {X Y : Systems.{c, v, r} J B τ}
    {m n : ℕ} (h : n ≤ m)
    (hm : (evaluation.{c, v, r} J B τ m).obj X = (evaluation.{c, v, r} J B τ m).obj Y)
    (hn : (evaluation.{c, v, r} J B τ n).obj X = (evaluation.{c, v, r} J B τ n).obj Y)
    (ht : (transition.{c, v, r} J B τ h).app X ≍ (transition.{c, v, r} J B τ h).app Y)
    (U : Cᵒᵖ) (x : X.val.obj (op (m, U.unop))) (y : Y.val.obj (op (m, U.unop)))
    (hxy : x ≍ y) :
    X.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x ≍
      Y.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op y := by
  have hsection := sheafOfModules_app_heq hm
    (congrArg (res.{c, v, r} (coefficientMap.{c, v, r} J B τ h)).obj hn)
    _ _ ht U x y hxy
  exact (heq_of_eq (transition_app_apply J B τ X h U x)).symm.trans
    (hsection.trans (heq_of_eq (transition_app_apply J B τ Y h U y)))

-- The membership checks of the restriction maps unfold the evaluation functors.
/-- A system is determined by its evaluations together with its transitions. -/
theorem system_ext {X Y : Systems.{c, v, r} J B τ}
    (he : ∀ n, (evaluation.{c, v, r} J B τ n).obj X = (evaluation.{c, v, r} J B τ n).obj Y)
    (ht : ∀ {m n : ℕ} (h : n ≤ m),
      (transition.{c, v, r} J B τ h).app X ≍ (transition.{c, v, r} J B τ h).app Y) :
    X = Y := by
  apply sheafOfModules_ext
  refine presheafOfModules_ext (funext fun ⟨⟨n, U⟩⟩ ↦ ?_) ?_
  · exact system_obj_eq_of_evaluation J B τ n (he n) (op U)
  · rintro ⟨⟨n, U⟩⟩ ⟨⟨m, V⟩⟩ g x y hxy
    have hg : g = (Prod.mkHom g.unop.1 (𝟙 U)).op ≫ ((Prod.sectR m C).map g.unop.2).op := by
      apply Quiver.Hom.unop_inj
      ext <;> simp
    rw [hg, PresheafOfModules.map_comp_apply, PresheafOfModules.map_comp_apply]
    apply system_vertical_map_heq J B τ m (he m) g.unop.2.op
    exact system_horizontal_map_heq J B τ (leOfHom g.unop.1)
      (he n) (he m) (ht _) (op U) x y hxy

/-- A morphism of systems is determined by its evaluations. -/
theorem system_hom_heq {X X' Y Y' : Systems.{c, v, r} J B τ} (hX : X = X') (hY : Y = Y')
    (a : X ⟶ Y) (b : X' ⟶ Y')
    (h : ∀ n, (evaluation.{c, v, r} J B τ n).map a ≍ (evaluation.{c, v, r} J B τ n).map b) :
    a ≍ b := by
  subst hX hY
  refine heq_of_eq (SheafOfModules.hom_ext (PresheafOfModules.hom_ext ?_))
  rintro ⟨⟨n, U⟩⟩
  ext x
  exact congrArg (fun φ ↦ φ.val.app (op U) x) (eq_of_heq (h n))

/-- Restriction of scalars along a ring endomorphism equal to the identity is the identity
on objects. -/
theorem res_obj_eq_self {A : Sheaf J CommRingCat.{r}} (φ : A ⟶ A) (hφ : φ = 𝟙 A)
    (X : Mod.{c, v, r} J A) : (res.{c, v, r} φ).obj X = X := by
  subst hφ
  rfl

/-- The sections of the transition are the horizontal restriction maps, stated as a
heterogeneous equality whose right-hand side lives in the sections of the system itself. -/
theorem transition_app_heq (X : Systems.{c, v, r} J B τ) {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ)
    (x : ((evaluation.{c, v, r} J B τ m).obj X).val.obj U) :
    @HEq _ (((transition.{c, v, r} J B τ h).app X).val.app U x) (X.val.obj (op (n, U.unop)))
      (X.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) :=
  heq_of_eq (transition_app_apply.{c, v, r} J B τ X h U x)

end Systems

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{max c v r})

/-- Constant coefficients, with the identity horizontal coefficient homomorphism. -/
def constantCoefficients : ℕ → Sheaf J CommRingCat.{max c v r} := fun _ ↦ R

/-- The identity coefficient transitions. -/
def constantCoefficientTransitions (n : ℕ) :
    constantCoefficients.{c, v, r} J R (n + 1) ⟶ constantCoefficients.{c, v, r} J R n := 𝟙 R

/-- A constant system keeps each module and each morphism at every vertex, and
its horizontal maps are the identity. Heterogeneous equality only suppresses
the restriction-of-scalars presentations of the same identity action. -/
def IsConstantSystemFunctor
    (F : Mod.{c, v, max c v r} J R ⥤
      Systems.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
      (constantCoefficientTransitions.{c, v, r} J R)) : Prop :=
  (∀ (M : Mod.{c, v, max c v r} J R) (n : ℕ),
    (evaluation.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
      (constantCoefficientTransitions.{c, v, r} J R) n).obj (F.obj M) = M) ∧
  (∀ {M N : Mod.{c, v, max c v r} J R} (f : M ⟶ N) (n : ℕ),
    HEq ((evaluation.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
      (constantCoefficientTransitions.{c, v, r} J R) n).map (F.map f)) f) ∧
  (∀ (M : Mod.{c, v, max c v r} J R) {m n : ℕ} (h : n ≤ m),
    HEq ((transition.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
      (constantCoefficientTransitions.{c, v, r} J R) h).app (F.obj M)) (𝟙 M))

/-- The zero vertical slice is left adjoint to the projection of the sequence site. -/
def sectZeroSndAdjunction : Prod.sectR 0 C ⊣ CategoryTheory.Prod.snd ℕ C :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ X :=
        { toFun f := f.2
          invFun g := Prod.mkHom (homOfLE (Nat.zero_le X.1)) g
          left_inv _ := Prod.hom_ext (Subsingleton.elim _ _) rfl
          right_inv _ := rfl } }

/-- The zero vertical slice is cocontinuous, since covers of the sequence site are
vertical. -/
instance sectZero_isCocontinuous :
    (Prod.sectR 0 C).IsCocontinuous J (coefficientSequenceTopology J) :=
  ⟨fun hS ↦ hS⟩

/-- The projection of the sequence site is cocontinuous. -/
instance snd_isCocontinuous :
    (CategoryTheory.Prod.snd ℕ C).IsCocontinuous (coefficientSequenceTopology J) J :=
  ⟨fun hS ↦ hS⟩

/-- The projection of the sequence site is continuous, being right adjoint to a
cocontinuous functor. -/
instance snd_isContinuous :
    (CategoryTheory.Prod.snd ℕ C).IsContinuous (coefficientSequenceTopology J) J :=
  (sectZeroSndAdjunction (C := C)).isContinuous_of_isCocontinuous J _

omit [EssentiallySmall.{max c v r} C] in
/-- All composite constant coefficient transitions are identities. -/
theorem constantRings_map_homOfLE {m n : ℕ} (h : n ≤ m) :
    (rings.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
      (constantCoefficientTransitions.{c, v, r} J R)).map (homOfLE h).op = 𝟙 R := by
  induction m, h using Nat.le_induction with
  | base => exact (rings.{c, v, max c v r} J _ _).map_id (op n)
  | succ m hnm ih =>
    rw [← homOfLE_comp hnm (Nat.le_add_right m 1), op_comp, Functor.map_comp, ih]
    simp only [rings, Functor.ofOpSequence_map_homOfLE_succ, constantCoefficientTransitions]
    exact Category.id_comp _

omit [EssentiallySmall.{max c v r} C] in
/-- All constant coefficient transitions are identities. -/
theorem constantRings_map {m n : ℕᵒᵖ} (g : m ⟶ n) :
    (rings.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
      (constantCoefficientTransitions.{c, v, r} J R)).map g = 𝟙 R :=
  (congrArg _ (Subsingleton.elim _ _)).trans
    (constantRings_map_homOfLE.{c, v, r} J R (leOfHom g.unop))

omit [EssentiallySmall.{max c v r} C] in
/-- The constant coefficient maps are identities. -/
theorem constantCoefficientMap {m n : ℕ} (h : n ≤ m) :
    coefficientMap.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
      (constantCoefficientTransitions.{c, v, r} J R) h = 𝟙 R :=
  constantRings_map_homOfLE.{c, v, r} J R h

omit [EssentiallySmall.{max c v r} C] in
/-- The constant ring system is `R` pulled back along the projection. -/
theorem constantRingPresheaf_map {X Y : (ℕ × C)ᵒᵖ} (f : X ⟶ Y) :
    (ringPresheaf.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
      (constantCoefficientTransitions.{c, v, r} J R)).map f = R.obj.map f.unop.2.op := by
  dsimp [ringPresheaf]
  rw [constantRings_map]
  exact Category.id_comp _

/-- The identity comparison of the constant ring system with `R` pulled back along the
projection of the sequence site. -/
def constantSystemRingMap :
    ring.{c, v, max c v r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
        (constantCoefficientTransitions.{c, v, r} J R)) ⟶
      ((CategoryTheory.Prod.snd ℕ C).sheafPushforwardContinuous RingCat.{max c v r}
        (coefficientSequenceTopology J) J).obj (ring.{c, v, max c v r} J R) :=
  ⟨{ app _ := 𝟙 _
     naturality _ _ f := by
       rw [Category.comp_id, Category.id_comp]
       exact congrArg (forget₂ CommRingCat RingCat).map
         (constantRingPresheaf_map.{c, v, r} J R f) }⟩

/-- The constant system: the module `M` at every level, with identity horizontal maps.
It is the pushforward along the projection `ℕ × C ⥤ C` of the sequence site. -/
def constantSystemPushforward : Mod.{c, v, max c v r} J R ⥤
      Systems.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
    (constantCoefficientTransitions.{c, v, r} J R) :=
  SheafOfModules.pushforward (constantSystemRingMap.{c, v, r} J R)

/-- Every evaluation of the constant system of `M` is `M`. -/
theorem constantSystemPushforward_evaluation_obj (M : Mod.{c, v, max c v r} J R) (n : ℕ) :
    (evaluation.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
      (constantCoefficientTransitions.{c, v, r} J R) n).obj
        ((constantSystemPushforward.{c, v, r} J R).obj M) = M := by
  refine sheafOfModules_ext (presheafOfModules_ext (funext fun U ↦
    moduleCat_restrictScalars_obj_eq_self _ (evaluation_ring_app.{c, v, max c v r} J
      (constantCoefficients.{c, v, r} J R) (constantCoefficientTransitions.{c, v, r} J R) n U)
      _) fun f x y hxy ↦ ?_)
  obtain rfl := eq_of_heq hxy
  exact HEq.rfl

/-- Every evaluation of the constant system of a morphism `f` is `f`. -/
theorem constantSystemPushforward_evaluation_map {M N : Mod.{c, v, max c v r} J R} (f : M ⟶ N)
    (n : ℕ) :
    (evaluation.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
      (constantCoefficientTransitions.{c, v, r} J R) n).map
        ((constantSystemPushforward.{c, v, r} J R).map f)
        ≍ f := by
  refine sheafOfModules_hom_heq (constantSystemPushforward_evaluation_obj.{c, v, r} J R M n)
    (constantSystemPushforward_evaluation_obj.{c, v, r} J R N n) _ _ fun U x y hxy ↦ ?_
  obtain rfl := eq_of_heq hxy
  exact HEq.rfl

/-- Restricting an evaluation of the constant system along a (trivial) coefficient map
gives back the original module. -/
theorem constantSystemPushforward_res_evaluation_obj (M : Mod.{c, v, max c v r} J R)
    {m n : ℕ} (h : n ≤ m) :
    (res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J
      (constantCoefficients.{c, v, r} J R) (constantCoefficientTransitions.{c, v, r} J R) h)).obj
      ((evaluation.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
        (constantCoefficientTransitions.{c, v, r} J R) n).obj
          ((constantSystemPushforward.{c, v, r} J R).obj M)) = M :=
  (res_obj_eq_self J _ (constantCoefficientMap.{c, v, r} J R h) _).trans
    (constantSystemPushforward_evaluation_obj.{c, v, r} J R M n)

/-- The horizontal restriction maps of the constant system are the identity on sections. -/
theorem constantSystemPushforward_val_map_heq (M : Mod.{c, v, max c v r} J R) {m n : ℕ}
    (h : n ≤ m) (V : C)
    (y : ((constantSystemPushforward.{c, v, r} J R).obj M).val.obj (op (m, V))) :
    @HEq (((constantSystemPushforward.{c, v, r} J R).obj M).val.obj (op (n, V)))
      (((constantSystemPushforward.{c, v, r} J R).obj M).val.map
        (Prod.mkHom (homOfLE h) (𝟙 V)).op y)
      (((constantSystemPushforward.{c, v, r} J R).obj M).val.obj (op (m, V))) y :=
  @heq_of_eq (M.val.obj (op V)) _ _ (congrArg (fun g ↦ g.hom y) (M.val.map_id (op V)))

/-- The transitions of the constant system are the identity on sections. -/
theorem constantSystemPushforward_transition_app_apply (M : Mod.{c, v, max c v r} J R)
    {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ)
    (x : ((evaluation.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
      (constantCoefficientTransitions.{c, v, r} J R) m).obj
        ((constantSystemPushforward.{c, v, r} J R).obj M)).val.obj U) :
    ((transition.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
      (constantCoefficientTransitions.{c, v, r} J R) h).app
        ((constantSystemPushforward.{c, v, r} J R).obj M)).val.app U x ≍ x :=
  (transition_app_heq.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
    (constantCoefficientTransitions.{c, v, r} J R)
    ((constantSystemPushforward.{c, v, r} J R).obj M) h U x).trans
    (constantSystemPushforward_val_map_heq.{c, v, r} J R M h U.unop x)

/-- The constant system satisfies its sectionwise characterization. -/
theorem constantSystemPushforward_isConstantSystemFunctor :
    IsConstantSystemFunctor.{c, v, r} J R (constantSystemPushforward.{c, v, r} J R) :=
  ⟨constantSystemPushforward_evaluation_obj.{c, v, r} J R,
    fun f n ↦ constantSystemPushforward_evaluation_map.{c, v, r} J R f n,
    fun M _ _ h ↦ sheafOfModules_heq_id_of_app
      (constantSystemPushforward_evaluation_obj.{c, v, r} J R M _)
      (constantSystemPushforward_res_evaluation_obj.{c, v, r} J R M h) _
      (constantSystemPushforward_transition_app_apply.{c, v, r} J R M h)⟩

/-- Additivity of the constant-system functor. -/
instance constantSystemPushforward_additive :
    (constantSystemPushforward.{c, v, r} J R).Additive where
  map_add := by
    intros
    ext U x
    rfl

/-- Left exactness of the constant-system functor: kernels are computed sectionwise. -/
instance constantSystemPushforward_limits :
    PreservesFiniteLimits (constantSystemPushforward.{c, v, r} J R) := by
  let T := SheafOfModules.forget.{max c v r} (ring.{c, v, max c v r}
      (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
        (constantCoefficientTransitions.{c, v, r} J R))) ⋙ PresheafOfModules.toPresheaf _
  have : PreservesFiniteLimits (constantSystemPushforward.{c, v, r} J R ⋙ T) :=
    inferInstanceAs (PreservesFiniteLimits
      ((SheafOfModules.forget.{max c v r} (ring.{c, v, max c v r} J R) ⋙
        PresheafOfModules.toPresheaf _) ⋙
          (Functor.whiskeringLeft _ _ _).obj (CategoryTheory.Prod.snd ℕ C).op))
  exact preservesFiniteLimits_of_reflects_of_preserves _ T

/-- Right exactness of the constant-system functor: pushforward along the continuous and
cocontinuous projection is a left adjoint on abelian sheaves. -/
instance constantSystemPushforward_colimits :
    PreservesFiniteColimits (constantSystemPushforward.{c, v, r} J R) := by
  have (F : (ℕ × C)ᵒᵖ ⥤ AddCommGrpCat.{max c v r}) :
      (CategoryTheory.Prod.snd ℕ C).op.HasPointwiseRightKanExtension F := fun X ↦ by
    have : HasLimitsOfShape (StructuredArrow X (CategoryTheory.Prod.snd ℕ C).op)
        AddCommGrpCat.{max c v r} :=
      HasLimitsOfShape.of_essentiallySmall _ _
    infer_instance
  let H := (CategoryTheory.Prod.snd ℕ C).sheafPushforwardContinuous AddCommGrpCat.{max c v r}
    (coefficientSequenceTopology J) J
  have : PreservesColimitsOfSize.{0, 0} H :=
    ((CategoryTheory.Prod.snd ℕ C).sheafAdjunctionCocontinuous AddCommGrpCat.{max c v r}
      (coefficientSequenceTopology J) J).leftAdjoint_preservesColimits
  let T := SheafOfModules.toSheaf.{max c v r} (ring.{c, v, max c v r}
      (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
        (constantCoefficientTransitions.{c, v, r} J R)))
  have : PreservesFiniteColimits (constantSystemPushforward.{c, v, r} J R ⋙ T) :=
    inferInstanceAs (PreservesFiniteColimits
      (SheafOfModules.toSheaf.{max c v r} (ring.{c, v, max c v r} J R) ⋙ H))
  have : ReflectsFiniteColimits T :=
    { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact preservesFiniteColimits_of_reflects_of_preserves _ T

/-- The constant module system is uniquely determined and is exact. -/
theorem constantSystem_existsUnique :
    (∃! F : Mod.{c, v, max c v r} J R ⥤
      Systems.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
      (constantCoefficientTransitions.{c, v, r} J R), IsConstantSystemFunctor.{c, v, r} J R F) ∧
    (∀ F : Mod.{c, v, max c v r} J R ⥤
      Systems.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
      (constantCoefficientTransitions.{c, v, r} J R), IsConstantSystemFunctor.{c, v, r} J R F →
      F.Additive ∧ PreservesFiniteLimits F ∧ PreservesFiniteColimits F) := by
  have huniq (F : Mod.{c, v, max c v r} J R ⥤
      Systems.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
      (constantCoefficientTransitions.{c, v, r} J R))
      (hF : IsConstantSystemFunctor.{c, v, r} J R F) :
      F = constantSystemPushforward.{c, v, r} J R := by
    have hC := constantSystemPushforward_isConstantSystemFunctor.{c, v, r} J R
    have hobj (M : Mod.{c, v, max c v r} J R) :
        F.obj M = (constantSystemPushforward.{c, v, r} J R).obj M :=
      system_ext.{c, v, max c v r} J _ _ (fun n ↦ (hF.1 M n).trans (hC.1 M n).symm)
        fun h ↦ (hF.2.2 M h).trans (hC.2.2 M h).symm
    exact Functor.hext hobj fun M N f ↦ system_hom_heq.{c, v, max c v r} J _ _ (hobj M)
      (hobj N) _ _ fun n ↦ (hF.2.1 f n).trans (hC.2.1 f n).symm
  refine ⟨⟨constantSystemPushforward.{c, v, r} J R,
    constantSystemPushforward_isConstantSystemFunctor.{c, v, r} J R,
    huniq⟩, fun F hF ↦ ?_⟩
  obtain rfl := huniq F hF
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The genuine diagonal functor, selected from its unique sectionwise characterization. -/
def constantSystem : Mod.{c, v, max c v r} J R ⥤
      Systems.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
    (constantCoefficientTransitions.{c, v, r} J R) :=
  (constantSystem_existsUnique.{c, v, r} J R).1.exists.choose

/-- Additivity of the genuine constant-system functor. -/
instance constantSystem_additive : (constantSystem.{c, v, r} J R).Additive :=
  ((constantSystem_existsUnique.{c, v, r} J R).2 _
    (constantSystem_existsUnique.{c, v, r} J R).1.exists.choose_spec).1

/-- Left exactness of the genuine constant-system functor. -/
instance constantSystem_limits : PreservesFiniteLimits (constantSystem.{c, v, r} J R) :=
  ((constantSystem_existsUnique.{c, v, r} J R).2 _
    (constantSystem_existsUnique.{c, v, r} J R).1.exists.choose_spec).2.1

/-- Right exactness of the genuine constant-system functor. -/
instance constantSystem_colimits : PreservesFiniteColimits (constantSystem.{c, v, r} J R) :=
  ((constantSystem_existsUnique.{c, v, r} J R).2 _
    (constantSystem_existsUnique.{c, v, r} J R).1.exists.choose_spec).2.2

/-- Termwise localization of the exact diagonal, before any coefficient extension. -/
def derivedConstantSystem : D.{c, v, max c v r} J R ⥤
    DS.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
    (constantCoefficientTransitions.{c, v, r} J R) :=
  (constantSystem.{c, v, r} J R).mapDerivedCategory

end WeilConjectures.SemilinearSections
