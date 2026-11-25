/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! Compatible families of local module sections, with restrictions indexed by all test objects.
Source: Stacks Project, Sites, Tag 04TR.
(auxiliary; not a blueprint node)

Instead of choosing fibre products, use all test spans `W → V`, `W → U i`. The equations
for restrictions identify this family with the usual product over the fibre products.
This presentation makes evaluation along a graph literal, even for nonmonomorphic covers.
-/

@[expose] public section
set_option autoImplicit false
universe uD vD uR w v uS
open CategoryTheory Opposite
namespace SheafOfModules

/-- Underlying local sections, as a type independently of the displayed scalar ring. -/
def moduleLocalSections {D : Type uD} [Category.{vD} D]
    {K : GrothendieckTopology D} {A : Sheaf K RingCat.{uR}}
    {I : Type w} {U : I → D}
    (F : ∀ i, SheafOfModules.{v} (A.over (U i))) (i : I) (V : Over (U i)) : Type v :=
  (F i).val.obj (op V)

instance {D : Type uD} [Category.{vD} D] {K : GrothendieckTopology D}
    {A : Sheaf K RingCat.{uR}} {I : Type w} {U : I → D}
    (F : ∀ i, SheafOfModules.{v} (A.over (U i))) (i : I) (V : Over (U i)) :
    AddCommGroup (moduleLocalSections F i V) :=
  inferInstanceAs (AddCommGroup ((F i).val.obj (op V)))

instance {D : Type uD} [Category.{vD} D] {K : GrothendieckTopology D}
    {A : Sheaf K RingCat.{uR}} {I : Type w} {U : I → D}
    (F : ∀ i, SheafOfModules.{v} (A.over (U i))) (i : I) (V : Over (U i))
    {R : Type uS} [Semiring R] [Module R ((F i).val.obj (op V))] :
    Module R (moduleLocalSections F i V) :=
  inferInstanceAs (Module R ((F i).val.obj (op V)))

/-- Linear gluing data on localizations of a ringed site.
Source: Stacks Project, Sites, Tag 04TR.
(auxiliary; not a blueprint node) -/
structure ModuleGlueData {D : Type uD} [Category.{vD} D]
    {K : GrothendieckTopology D} (A : Sheaf K RingCat.{uR})
    {I : Type w} (U : I → D) where
  localSheaf : ∀ i, SheafOfModules.{max uD vD w v} (A.over (U i))
  transition : ∀ i j (W : D) (a : W ⟶ U i) (b : W ⟶ U j),
    moduleLocalSections localSheaf i (Over.mk a) ≃+
      moduleLocalSections localSheaf j (Over.mk b)
  transition_smul : ∀ i j (W : D) (a : W ⟶ U i) (b : W ⟶ U j)
    (r : A.obj.obj (op W)) (x : moduleLocalSections localSheaf i (Over.mk a)),
    transition i j W a b (r • x) = r • transition i j W a b x
  naturality : ∀ i j (W V : D) (k : V ⟶ W) (a : W ⟶ U i) (b : W ⟶ U j)
    (x : moduleLocalSections localSheaf i (Over.mk a)),
    transition i j V (k ≫ a) (k ≫ b)
      ((localSheaf i).val.map
        (Over.homMk (U := Over.mk (k ≫ a)) (V := Over.mk a) k rfl).op x) =
      (localSheaf j).val.map
        (Over.homMk (U := Over.mk (k ≫ b)) (V := Over.mk b) k rfl).op
          (transition i j W a b x)
  cocycle : ∀ i j k (W : D) (a : W ⟶ U i) (b : W ⟶ U j) (c : W ⟶ U k)
    (x : moduleLocalSections localSheaf i (Over.mk a)),
    transition i k W a c x = transition j k W b c (transition i j W a b x)

namespace ModuleGlueData
variable {D : Type uD} [Category.{vD} D] {K : GrothendieckTopology D}
  {A : Sheaf K RingCat.{uR}} {I : Type w} {U : I → D}
  (G : ModuleGlueData.{uD, vD, uR, w, v} A U)

/-- The restriction function, with its unchanged underlying type made explicit. -/
noncomputable def res (i : I) {V W : Over (U i)} (f : W ⟶ V)
    (x : moduleLocalSections G.localSheaf i V) : moduleLocalSections G.localSheaf i W :=
  (G.localSheaf i).val.map f.op x

@[simp] lemma res_zero (i : I) {V W : Over (U i)} (f : W ⟶ V) :
    G.res i f 0 = 0 := map_zero _

@[simp] lemma res_add (i : I) {V W : Over (U i)} (f : W ⟶ V) (x y) :
    G.res i f (x + y) = G.res i f x + G.res i f y := map_add _ _ _

lemma res_smul (i : I) {V W : Over (U i)} (f : W ⟶ V)
    (r : A.obj.obj (op V.left)) (x) :
    G.res i f (r • x) = A.obj.map f.left.op r • G.res i f x :=
  (G.localSheaf i).val.map_smul f.op r x

@[simp] lemma res_id (i : I) (V : Over (U i)) (x) : G.res i (𝟙 V) x = x := by
  change (G.localSheaf i).val.map (𝟙 _) x = x
  rw [PresheafOfModules.map_id]
  rfl

lemma res_comp (i : I) {V W T : Over (U i)} (f : W ⟶ V) (g : T ⟶ W) (x) :
    G.res i (g ≫ f) x = G.res i g (G.res i f x) :=
  (G.localSheaf i).val.map_comp_apply f.op g.op x

lemma res_naturality (i j : I) (W V : D) (k : V ⟶ W)
    (a : W ⟶ U i) (b : W ⟶ U j) (x) :
    G.transition i j V (k ≫ a) (k ≫ b)
      (G.res i (Over.homMk (U := Over.mk (k ≫ a)) (V := Over.mk a) k rfl) x) =
      G.res j (Over.homMk (U := Over.mk (k ≫ b)) (V := Over.mk b) k rfl)
        (G.transition i j W a b x) := G.naturality i j W V k a b x

lemma transition_res_congr (i j : I) (W : D) (V : Over (U i)) (f : W ⟶ V.left)
    (a a' : W ⟶ U i) (ha : f ≫ V.hom = a) (ha' : f ≫ V.hom = a')
    (b : W ⟶ U j) (s : moduleLocalSections G.localSheaf i V) :
    G.transition i j W a b (G.res i
      (Over.homMk (U := Over.mk a) (V := V) f ha) s) =
      G.transition i j W a' b (G.res i
        (Over.homMk (U := Over.mk a') (V := V) f ha') s) := by
  have h : a = a' := ha.symm.trans ha'
  cases h
  rfl

lemma transition_self (i : I) (W : D) (a : W ⟶ U i)
    (x : moduleLocalSections G.localSheaf i (Over.mk a)) :
    G.transition i i W a a x = x := by
  apply (G.transition i i W a a).injective
  simpa using (G.cocycle i i i W a a a x).symm

/-- A test section over `V` lies over some `W → V` and `W → U i`. -/
abbrev Index (U : I → D) (V : D) := Σ i : I, Σ W : D, (W ⟶ V) × (W ⟶ U i)

/-- The module of all families, before imposing compatibility. -/
abbrev Ambient (V : D) := ∀ q : Index U V,
  (ModuleCat.restrictScalars (A.obj.map q.2.2.1.op).hom).obj
    ((G.localSheaf q.1).val.obj (op (Over.mk q.2.2.2)))

/-- The compatible families form a submodule of the product of the local modules. -/
def tuples (V : D) : Submodule (A.obj.obj (op V)) (G.Ambient V) where
  carrier := {x | (∀ i (W T : D) (k : T ⟶ W) (f : W ⟶ V) (a : W ⟶ U i),
      G.res i (Over.homMk (U := Over.mk (k ≫ a)) (V := Over.mk a) k rfl) (x ⟨i, W, f, a⟩) =
        x ⟨i, T, k ≫ f, k ≫ a⟩) ∧
    (∀ i j (W : D) (f : W ⟶ V) (a : W ⟶ U i) (b : W ⟶ U j),
      G.transition i j W a b (x ⟨i, W, f, a⟩) = x ⟨j, W, f, b⟩)}
  zero_mem' := by constructor <;> intros <;> simp
  add_mem' := by
    intro x y hx hy
    constructor
    · intro i W T k f a
      simp only [Pi.add_apply, G.res_add, hx.1, hy.1]
    · intro i j W f a b
      simp only [Pi.add_apply, map_add, hx.2, hy.2]
  smul_mem' := by
    intro r x hx
    constructor
    · intro i W T k f a
      change G.res i (Over.homMk (U := Over.mk (k ≫ a)) (V := Over.mk a) k rfl)
        (A.obj.map f.op r • x ⟨i, W, f, a⟩) =
        A.obj.map (k ≫ f).op r • x ⟨i, T, k ≫ f, k ≫ a⟩
      rw [G.res_smul, hx.1]
      congr 1
      change A.obj.map k.op (A.obj.map f.op r) = A.obj.map (k ≫ f).op r
      simp [Functor.map_comp]
    · intro i j W f a b
      change G.transition i j W a b (A.obj.map f.op r • x ⟨i, W, f, a⟩) =
        A.obj.map f.op r • x ⟨j, W, f, b⟩
      rw [G.transition_smul, hx.2]

/-- Restriction precomposes the arrow to the object where the family is taken. -/
def restrict {V W : D} (g : W ⟶ V) (x : G.tuples V) : G.tuples W :=
  ⟨fun q ↦ x.1 ⟨q.1, q.2.1, q.2.2.1 ≫ g, q.2.2.2⟩, by
    constructor
    · intro i T S k f a
      change G.res i (Over.homMk (U := Over.mk (k ≫ a)) (V := Over.mk a) k rfl)
        (x.1 ⟨i, T, f ≫ g, a⟩) = x.1 ⟨i, S, (k ≫ f) ≫ g, k ≫ a⟩
      rw [Category.assoc]
      exact x.2.1 i T S k (f ≫ g) a
    · intro i j T f a b
      exact x.2.2 i j T (f ≫ g) a b⟩

/-- The presheaf of compatible local module sections. -/
noncomputable def presheaf : PresheafOfModules.{max uD vD w v} A.obj where
  obj V := ModuleCat.of _ (G.tuples V.unop)
  map {V W} g := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (A.obj.map g).hom).obj
      (ModuleCat.of _ (G.tuples W.unop)))
    { toFun := G.restrict g.unop
      map_add' := by intros; rfl
      map_smul' := by
        intro r x
        apply Subtype.ext
        funext q
        change A.obj.map (q.2.2.1 ≫ g.unop).op r •
            x.1 ⟨q.1, q.2.1, q.2.2.1 ≫ g.unop, q.2.2.2⟩ =
          A.obj.map q.2.2.1.op (A.obj.map g r) •
            x.1 ⟨q.1, q.2.1, q.2.2.1 ≫ g.unop, q.2.2.2⟩
        simp [Functor.map_comp] }
  map_id V := by
    ext x
    apply Subtype.ext
    funext q
    change x.1 ⟨q.1, q.2.1, q.2.2.1 ≫ 𝟙 _, q.2.2.2⟩ = x.1 q
    rcases q with ⟨i, T, f, a⟩
    change (x.1 ⟨i, T, f ≫ 𝟙 _, a⟩ : moduleLocalSections G.localSheaf i (Over.mk a)) =
      x.1 ⟨i, T, f, a⟩
    rw [Category.comp_id]
  map_comp f g := by
    ext x
    apply Subtype.ext
    funext q
    change x.1 ⟨q.1, q.2.1, q.2.2.1 ≫ (g.unop ≫ f.unop), q.2.2.2⟩ =
      x.1 ⟨q.1, q.2.1, (q.2.2.1 ≫ g.unop) ≫ f.unop, q.2.2.2⟩
    rw [Category.assoc]

/-- Restrict a local section to a test object. -/
noncomputable abbrev localRestrict (i : I) {W T : D} (a : W ⟶ U i) (k : T ⟶ W)
    (x : moduleLocalSections G.localSheaf i (Over.mk a)) :=
  G.res i (Over.homMk (U := Over.mk (k ≫ a)) (V := Over.mk a) k rfl) x

/-- Evaluation along the graph of a local object. -/
def evaluate (i : I) (V : Over (U i)) (x : G.tuples V.left) :
    moduleLocalSections G.localSheaf i V :=
  x.1 ⟨i, V.left, 𝟙 _, V.hom⟩

/-- A local section extends to its family of transition images on all test objects. -/
noncomputable def extend (i : I) (V : Over (U i)) (s : moduleLocalSections G.localSheaf i V) :
    G.tuples V.left :=
  ⟨fun q ↦ G.transition i q.1 q.2.1 (q.2.2.1 ≫ V.hom) q.2.2.2
      (G.res i (Over.homMk (U := Over.mk (q.2.2.1 ≫ V.hom)) (V := V) q.2.2.1 rfl) s), by
    constructor
    · intro j W T k f a
      change G.localRestrict j a k
        (G.transition i j W (f ≫ V.hom) a
          (G.res i (Over.homMk (U := Over.mk (f ≫ V.hom)) (V := V) f rfl) s)) = _
      dsimp only [localRestrict]
      have h := (G.res_naturality i j W T k (f ≫ V.hom) a
        (G.res i (Over.homMk (U := Over.mk (f ≫ V.hom)) (V := V) f rfl) s)).symm
      apply h.trans
      rw [← G.res_comp]
      have he : (Over.homMk (U := Over.mk (k ≫ f ≫ V.hom))
          (V := Over.mk (f ≫ V.hom)) k rfl) ≫
          (Over.homMk (U := Over.mk (f ≫ V.hom)) (V := V) f rfl) =
          Over.homMk (U := Over.mk (k ≫ f ≫ V.hom)) (V := V)
            (k ≫ f) (Category.assoc _ _ _) := by ext; rfl
      rw [he]
      exact G.transition_res_congr i j T V (k ≫ f) _ _ (Category.assoc _ _ _)
        rfl (k ≫ a) s
    · intro j k W f a b
      exact (G.cocycle i j k W (f ≫ V.hom) a b
        (G.res i (Over.homMk (U := Over.mk (f ≫ V.hom)) (V := V) f rfl) s)).symm⟩

lemma evaluate_extend (i : I) (V : Over (U i))
    (s : moduleLocalSections G.localSheaf i V) : G.evaluate i V (G.extend i V s) = s := by
  change G.transition i i V.left (𝟙 _ ≫ V.hom) V.hom
    (G.res i (Over.homMk (U := Over.mk (𝟙 _ ≫ V.hom)) (V := V) (𝟙 _) (by simp)) s) = s
  calc
    _ = G.transition i i V.left V.hom V.hom (G.res i
        (Over.homMk (U := V) (V := V) (𝟙 _) (Category.id_comp _)) s) :=
      G.transition_res_congr i i V.left V (𝟙 _) _ _ rfl (Category.id_comp _) V.hom s
    _ = s := by
      change G.transition i i V.left V.hom V.hom (G.res i (𝟙 V) s) = s
      rw [G.res_id, G.transition_self]

lemma extend_evaluate (i : I) (V : Over (U i)) (x : G.tuples V.left) :
    G.extend i V (G.evaluate i V x) = x := by
  apply Subtype.ext
  funext q
  rcases q with ⟨j, W, f, a⟩
  change G.transition i j W (f ≫ V.hom) a
    (G.res i (Over.homMk (U := Over.mk (f ≫ V.hom)) (V := V) f rfl)
      (x.1 ⟨i, V.left, 𝟙 _, V.hom⟩)) = x.1 ⟨j, W, f, a⟩
  erw [x.2.1 i V.left W f (𝟙 _) V.hom]
  erw [Category.comp_id]
  exact x.2.2 i j W f (f ≫ V.hom) a

lemma tuple_res (V : D) (x : G.tuples V) (i : I) (W T : D)
    (k : T ⟶ W) (f : W ⟶ V) (a : W ⟶ U i) (b : T ⟶ U i) (hb : k ≫ a = b) :
    G.res i (Over.homMk (U := Over.mk b) (V := Over.mk a) k hb)
      (x.1 ⟨i, W, f, a⟩) = x.1 ⟨i, T, k ≫ f, b⟩ := by
  cases hb
  exact x.2.1 i W T k f a

lemma evaluate_naturality (i : I) {V W : Over (U i)} (f : W ⟶ V)
    (x : G.tuples V.left) :
    G.evaluate i W (G.restrict f.left x) = G.res i f (G.evaluate i V x) := by
  change (x.1 ⟨i, W.left, 𝟙 _ ≫ f.left, W.hom⟩ :
    moduleLocalSections G.localSheaf i W) = _
  have h := G.tuple_res V.left x i V.left W.left f.left (𝟙 _) V.hom W.hom (Over.w f)
  change G.res i f (G.evaluate i V x) = x.1 ⟨i, W.left, f.left ≫ 𝟙 _, W.hom⟩ at h
  apply Eq.trans _ h.symm
  exact congrArg (β := moduleLocalSections G.localSheaf i W) (fun g : W.left ⟶ V.left ↦
    (x.1 ⟨i, W.left, g, W.hom⟩ : moduleLocalSections G.localSheaf i W))
      ((Category.id_comp _).trans (Category.comp_id _).symm)

/-- Evaluation and extension give a linear equivalence on every local object. -/
noncomputable def componentEquiv (i : I) (V : Over (U i)) :
    G.tuples V.left ≃ₗ[A.obj.obj (op V.left)] moduleLocalSections G.localSheaf i V where
  toFun := G.evaluate i V
  invFun := G.extend i V
  left_inv := G.extend_evaluate i V
  right_inv := G.evaluate_extend i V
  map_add' _ _ := rfl
  map_smul' r x := by
    have hr : (A.obj.map (𝟙 (op V.left))).hom r = r := by
      rw [A.obj.map_id]
      rfl
    dsimp [evaluate, moduleLocalSections]
    exact congrArg (β := moduleLocalSections G.localSheaf i V)
      (fun t : A.obj.obj (op V.left) ↦ t • G.evaluate i V x) hr

/-- The actual compatible-family module sheaf, once its sheaf axiom is supplied. -/
noncomputable def sheaf (hs : Presheaf.IsSheaf K G.presheaf.presheaf) : SheafOfModules A :=
  ⟨G.presheaf, hs⟩

/-- The local identifications of the compatible-family module sheaf. -/
noncomputable def overIso (hs : Presheaf.IsSheaf K G.presheaf.presheaf) (i : I) :
    (G.sheaf hs).over (U i) ≅ G.localSheaf i :=
  (fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk (fun V ↦ (G.componentEquiv i V.unop).toModuleIso) (by
      intro V W f
      ext x
      exact G.evaluate_naturality i f.unop x)

/-- The underlying presheaf of local section types, using the restriction API. -/
noncomputable def localTypes (i : I) : (Over (U i))ᵒᵖ ⥤ Type (max uD vD w v) where
  obj V := moduleLocalSections G.localSheaf i V.unop
  map f := ↾(G.res i f.unop)
  map_id V := by ext x; exact G.res_id i V.unop x
  map_comp f g := by ext x; exact G.res_comp i f.unop g.unop x

lemma localTypes_isSheaf (i : I) : Presieve.IsSheaf (K.over (U i)) (G.localTypes i) := by
  change Presieve.IsSheaf (K.over (U i))
    ((G.localSheaf i).val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat)
  exact (isSheaf_iff_isSheaf_of_type _ _).mp
    (Presheaf.isSheaf_comp_of_isSheaf (K.over (U i)) (G.localSheaf i).val.presheaf
      (CategoryTheory.forget AddCommGrpCat.{max uD vD w v}) (G.localSheaf i).isSheaf)

/-- The underlying type presheaf of compatible tuples, using literal restriction functions. -/
noncomputable def types : Dᵒᵖ ⥤ Type (max uD vD w v) where
  obj V := G.tuples V.unop
  map f := ↾(G.restrict f.unop)
  map_id V := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    funext q
    dsimp [restrict]
    rw [Category.comp_id]
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    funext q
    dsimp [restrict]
    rw [Category.assoc]

/-- The covering sieve seen by one test object in a compatible tuple. -/
def localSieve {V : D} (S : Sieve V) {W : D} (f : W ⟶ V) {i : I} (a : W ⟶ U i) :
    Sieve (Over.mk a) := (Sieve.overEquiv (Over.mk a)).symm (S.pullback f)

lemma localSieve_mem {V : D} (S : Sieve V) (hS : S ∈ K V) {W : D} (f : W ⟶ V)
    {i : I} (a : W ⟶ U i) : localSieve S f a ∈ (K.over (U i)) (Over.mk a) :=
  K.overEquiv_symm_mem_over _ _ (K.pullback_stable f hS)

/-- Evaluate a matching tuple family on one local slice. -/
noncomputable def localFamily {V : D} (S : Sieve V)
    (x : S.arrows.FamilyOfElements G.types) {W : D} (f : W ⟶ V)
    (i : I) (a : W ⟶ U i) :
    (localSieve S f a).arrows.FamilyOfElements (G.localTypes i) :=
  fun T k hk ↦ G.evaluate i T (x (k.left ≫ f) hk)

lemma localFamily_compatible {V : D} (S : Sieve V)
    (x : S.arrows.FamilyOfElements G.types) (hx : x.Compatible) {W : D} (f : W ⟶ V)
    (i : I) (a : W ⟶ U i) : (G.localFamily S x f i a).Compatible := by
  intro T₁ T₂ Z g₁ g₂ k₁ k₂ hk₁ hk₂ h
  have hh : g₁.left ≫ (k₁.left ≫ f) = g₂.left ≫ (k₂.left ≫ f) := by
    have hl := congrArg Over.Hom.left h
    simpa only [Over.comp_left, Category.assoc] using congrArg (fun t ↦ t ≫ f) hl
  have ht := hx g₁.left g₂.left
    hk₁
    hk₂ hh
  change G.res i g₁ (G.evaluate i T₁ (x (k₁.left ≫ f) _)) =
    G.res i g₂ (G.evaluate i T₂ (x (k₂.left ≫ f) _))
  rw [← G.evaluate_naturality, ← G.evaluate_naturality]
  exact congrArg (G.evaluate i Z) ht

/-- The unique glued section for one coordinate. Its uniqueness is the local sheaf axiom. -/
noncomputable def gluedCoordinate {V : D} (S : Sieve V) (hS : S ∈ K V)
    (x : S.arrows.FamilyOfElements G.types) (hx : x.Compatible) {W : D} (f : W ⟶ V)
    (i : I) (a : W ⟶ U i) : moduleLocalSections G.localSheaf i (Over.mk a) :=
  ((G.localTypes_isSheaf i) _ (localSieve_mem S hS f a)).amalgamate
    (G.localFamily S x f i a) (G.localFamily_compatible S x hx f i a)

lemma gluedCoordinate_restrict {V : D} (S : Sieve V) (hS : S ∈ K V)
    (x : S.arrows.FamilyOfElements G.types) (hx : x.Compatible) {W : D} (f : W ⟶ V)
    (i : I) (a : W ⟶ U i) {T : Over (U i)} (k : T ⟶ Over.mk a)
    (hk : S (k.left ≫ f)) :
    G.res i k (G.gluedCoordinate S hS x hx f i a) =
      G.evaluate i T (x (k.left ≫ f) hk) :=
  ((G.localTypes_isSheaf i) _ (localSieve_mem S hS f a)).valid_glue
    (G.localFamily_compatible S x hx f i a) k
      hk

lemma res_transition (i j : I) (W : D) (a : W ⟶ U i) (b : W ⟶ U j)
    (T : Over (U j)) (k : T ⟶ Over.mk b)
    (x : moduleLocalSections G.localSheaf i (Over.mk a)) :
    G.res j k (G.transition i j W a b x) =
      G.transition i j T.left (k.left ≫ a) T.hom
        (G.res i (Over.homMk (U := Over.mk (k.left ≫ a))
          (V := Over.mk a) k.left rfl) x) := by
  obtain ⟨T, c, rfl⟩ := Over.mk_surjective T
  obtain ⟨l, hl, rfl⟩ := Over.homMk_surjective k
  change T ⟶ W at l
  change l ≫ b = c at hl
  subst c
  exact (G.res_naturality i j W T l a b x).symm

lemma gluedCoordinate_transition {V : D} (S : Sieve V) (hS : S ∈ K V)
    (x : S.arrows.FamilyOfElements G.types) (hx : x.Compatible) {W : D}
    (f : W ⟶ V) (i j : I) (a : W ⟶ U i) (b : W ⟶ U j) :
    G.transition i j W a b (G.gluedCoordinate S hS x hx f i a) =
      G.gluedCoordinate S hS x hx f j b := by
  apply ((G.localTypes_isSheaf j) _ (localSieve_mem S hS f b)).isSeparatedFor.ext
  intro P l hl
  change G.res j l (G.transition i j W a b (G.gluedCoordinate S hS x hx f i a)) =
    G.res j l (G.gluedCoordinate S hS x hx f j b)
  rw [G.res_transition i j W a b P l]
  rw [G.gluedCoordinate_restrict S hS x hx f i a
    (Over.homMk (U := Over.mk (l.left ≫ a)) (V := Over.mk a) l.left rfl) hl]
  rw [G.gluedCoordinate_restrict S hS x hx f j b l hl]
  exact (x (l.left ≫ f) hl).2.2 i j P.left (𝟙 _) (l.left ≫ a) P.hom

lemma gluedCoordinate_naturality {V : D} (S : Sieve V) (hS : S ∈ K V)
    (x : S.arrows.FamilyOfElements G.types) (hx : x.Compatible) {W T : D}
    (f : W ⟶ V) (i : I) (a : W ⟶ U i) (k : T ⟶ W) :
    G.res i (Over.homMk (U := Over.mk (k ≫ a)) (V := Over.mk a) k rfl)
      (G.gluedCoordinate S hS x hx f i a) =
        G.gluedCoordinate S hS x hx (k ≫ f) i (k ≫ a) := by
  apply ((G.localTypes_isSheaf i) _
    (localSieve_mem S hS (k ≫ f) (k ≫ a))).isSeparatedFor.ext
  intro P l hl
  change S (l.left ≫ (k ≫ f)) at hl
  change G.res i l (G.res i (Over.homMk
    (U := Over.mk (k ≫ a)) (V := Over.mk a) k rfl)
    (G.gluedCoordinate S hS x hx f i a)) =
      G.res i l (G.gluedCoordinate S hS x hx (k ≫ f) i (k ≫ a))
  rw [← G.res_comp]
  rw [G.gluedCoordinate_restrict S hS x hx f i a
    (l ≫ Over.homMk (U := Over.mk (k ≫ a)) (V := Over.mk a) k rfl)
    (by simpa only [Over.comp_left, Over.homMk_left, Category.assoc] using hl)]
  rw [G.gluedCoordinate_restrict S hS x hx (k ≫ f) i (k ≫ a) l hl]
  congr 2
  exact Category.assoc l.left k f

lemma gluedCoordinate_of_mem {V : D} (S : Sieve V) (hS : S ∈ K V)
    (x : S.arrows.FamilyOfElements G.types) (hx : x.Compatible) {W : D}
    (f : W ⟶ V) (hf : S f) (i : I) (a : W ⟶ U i) :
    G.gluedCoordinate S hS x hx f i a = G.evaluate i (Over.mk a) (x f hf) := by
  have h := G.gluedCoordinate_restrict S hS x hx f i a (𝟙 (Over.mk a))
    (by simpa only [Over.id_left, Category.id_comp] using hf)
  rw [G.res_id] at h
  change G.gluedCoordinate S hS x hx f i a =
    G.evaluate i (Over.mk a) (x (𝟙 W ≫ f) _) at h
  convert h using 1
  congr 2
  exact (Category.id_comp f).symm

/-- The coordinates glued in the local sheaves form a compatible global tuple. -/
noncomputable def gluedTuple {V : D} (S : Sieve V) (hS : S ∈ K V)
    (x : S.arrows.FamilyOfElements G.types) (hx : x.Compatible) : G.tuples V :=
  ⟨fun q ↦ G.gluedCoordinate S hS x hx q.2.2.1 q.1 q.2.2.2, by
    constructor
    · intro i W T k f a
      exact G.gluedCoordinate_naturality S hS x hx f i a k
    · intro i j W f a b
      exact G.gluedCoordinate_transition S hS x hx f i j a b⟩

lemma evaluate_restrict (i : I) (P : Over (U i)) {V : D} (f : P.left ⟶ V)
    (x : G.tuples V) : G.evaluate i P (G.restrict f x) =
      x.1 ⟨i, P.left, f, P.hom⟩ := by
  change (x.1 ⟨i, P.left, 𝟙 _ ≫ f, P.hom⟩ :
    moduleLocalSections G.localSheaf i P) = _
  exact congrArg (β := moduleLocalSections G.localSheaf i P)
    (fun g : P.left ⟶ V ↦ (x.1 ⟨i, P.left, g, P.hom⟩ :
      moduleLocalSections G.localSheaf i P)) (Category.id_comp f)

lemma gluedTuple_amalgamation {V : D} (S : Sieve V) (hS : S ∈ K V)
    (x : S.arrows.FamilyOfElements G.types) (hx : x.Compatible) :
    x.IsAmalgamation (G.gluedTuple S hS x hx) := by
  intro W f hf
  apply Subtype.ext
  funext q
  rcases q with ⟨i, T, k, a⟩
  change G.gluedCoordinate S hS x hx (k ≫ f) i a = (x f hf).1 ⟨i, T, k, a⟩
  rw [G.gluedCoordinate_of_mem S hS x hx (k ≫ f) (S.downward_closed hf k) i a]
  have h := hx.to_sieveCompatible f k hf
  change x (k ≫ f) _ = G.restrict k (x f hf) at h
  rw [h]
  exact G.evaluate_restrict i (Over.mk a) k (x f hf)

lemma types_separated {V : D} (S : Sieve V) (hS : S ∈ K V) :
    Presieve.IsSeparatedFor G.types S.arrows := by
  intro x t₁ t₂ ht₁ ht₂
  apply Subtype.ext
  funext q
  rcases q with ⟨i, W, f, a⟩
  apply ((G.localTypes_isSheaf i) _ (localSieve_mem S hS f a)).isSeparatedFor.ext
  intro P k hk
  change S (k.left ≫ f) at hk
  change G.res i k (t₁.1 ⟨i, W, f, a⟩) = G.res i k (t₂.1 ⟨i, W, f, a⟩)
  have h₁ := G.tuple_res V t₁ i W P.left k.left f a P.hom (Over.w k)
  have h₂ := G.tuple_res V t₂ i W P.left k.left f a P.hom (Over.w k)
  change G.res i k (t₁.1 ⟨i, W, f, a⟩) = t₁.1 ⟨i, P.left, k.left ≫ f, P.hom⟩ at h₁
  change G.res i k (t₂.1 ⟨i, W, f, a⟩) = t₂.1 ⟨i, P.left, k.left ≫ f, P.hom⟩ at h₂
  rw [h₁, h₂]
  have h : G.restrict (k.left ≫ f) t₁ = G.restrict (k.left ≫ f) t₂ :=
    (ht₁ (k.left ≫ f) hk).trans (ht₂ (k.left ≫ f) hk).symm
  have he := congrArg (G.evaluate i P) h
  simpa only [G.evaluate_restrict] using he

/-- Compatible tuples satisfy the sheaf condition, since each local module is a sheaf. -/
theorem types_isSheaf : Presieve.IsSheaf K G.types := by
  intro V S hS
  apply (G.types_separated S hS).isSheafFor
  intro x hx
  exact ⟨G.gluedTuple S hS x hx, G.gluedTuple_amalgamation S hS x hx⟩

/-- The compatible-tuples module presheaf is a sheaf.

Source: Stacks Project, Sites, Tag 04TR. Glue each test-coordinate along the pulled-back
covering sieve in the corresponding local sheaf. Local separatedness proves that these
sections respect restrictions and transition maps. The glued tuple is an amalgamation by
matching-family compatibility, and uniqueness is checked in every local sheaf.
(auxiliary; not a blueprint node)
-/
theorem presheaf_isSheaf : Presheaf.IsSheaf K G.presheaf.presheaf := by
  apply Presheaf.isSheaf_of_isSheaf_comp K G.presheaf.presheaf
    (CategoryTheory.forget AddCommGrpCat.{max uD vD w v})
  exact (isSheaf_iff_isSheaf_of_type _ _).mpr G.types_isSheaf

end ModuleGlueData
end SheafOfModules
