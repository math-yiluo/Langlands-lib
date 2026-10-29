import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleStatement
import Langlands.AlgebraicGeometry.Picard.LineBundleDescent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule

/-! # Line bundles glued from unit cocycles -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.CocycleGluing

open Langlands.SchemeModule Langlands.SchemeModule.LineBundleDescent

variable {X : Scheme.{u}}

lemma res_res {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)) :
    X.presheaf.map (homOfLE h').op (X.presheaf.map (homOfLE h).op a) =
      X.presheaf.map (homOfLE (h'.trans h)).op a := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma res_self {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)) :
    X.presheaf.map (homOfLE h).op a = a := by
  have e : (homOfLE h).op = 𝟙 (op U) := rfl
  rw [e, CategoryTheory.Functor.map_id]
  rfl

/-- Two functions on `V` agree if they agree on a neighbourhood of each point of `V`. -/
lemma eq_of_local {V : X.Opens} (a b : Γ(X, V))
    (h : ∀ x ∈ V, ∃ W : X.Opens, ∃ hW : W ≤ V, x ∈ W ∧
      X.presheaf.map (homOfLE hW).op a = X.presheaf.map (homOfLE hW).op b) : a = b := by
  choose W hW hxW hab using h
  exact X.sheaf.eq_of_locally_eq' (fun x : V ↦ W x.1 x.2) V (fun x ↦ homOfLE (hW x.1 x.2))
    (fun x hx ↦ Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW x hx⟩) a b (fun x ↦ hab x.1 x.2)

variable {ι : Type u} (T : ι → X.Opens)

/-- Families of functions on the pieces `U ⊓ T i` of an open `U`. -/
def Fam (U : X.Opens) : Type u := ∀ i, Γ(X, U ⊓ T i)

instance (U : X.Opens) : AddCommGroup (Fam T U) :=
  inferInstanceAs (AddCommGroup (∀ i, Γ(X, U ⊓ T i)))

instance (U : X.Opens) : Module Γ(X, U) (Fam T U) where
  smul r b := fun i ↦ X.presheaf.map (homOfLE inf_le_left : U ⊓ T i ⟶ U).op r * b i
  one_smul b := funext fun i ↦ by
    change X.presheaf.map _ 1 * b i = b i
    rw [map_one, one_mul]
  mul_smul r s b := funext fun i ↦ by
    change X.presheaf.map _ (r * s) * b i = X.presheaf.map _ r * (X.presheaf.map _ s * b i)
    rw [map_mul, mul_assoc]
  smul_zero r := funext fun i ↦ mul_zero (X.presheaf.map _ r)
  smul_add r b c := funext fun i ↦ mul_add (X.presheaf.map _ r) (b i) (c i)
  add_smul r s b := funext fun i ↦ by
    change X.presheaf.map _ (r + s) * b i = X.presheaf.map _ r * b i + X.presheaf.map _ s * b i
    rw [map_add, add_mul]
  zero_smul b := funext fun i ↦ by
    change X.presheaf.map _ 0 * b i = 0
    rw [map_zero, zero_mul]

variable {T} in
lemma Fam.smul_apply {U : X.Opens} (r : Γ(X, U)) (b : Fam T U) (i : ι) :
    (r • b) i = X.presheaf.map (homOfLE inf_le_left : U ⊓ T i ⟶ U).op r * b i := rfl

variable {T} in
lemma Fam.add_apply {U : X.Opens} (b c : Fam T U) (i : ι) : (b + c) i = b i + c i := rfl

variable {T} in
lemma Fam.zero_apply {U : X.Opens} (i : ι) : (0 : Fam T U) i = 0 := rfl

/-- Componentwise restriction of families. -/
def famRes {U V : X.Opens} (h : V ≤ U) (b : Fam T U) : Fam T V :=
  fun i ↦ X.presheaf.map (homOfLE (inf_le_inf_right (T i) h)).op (b i)

variable {T} in
lemma famRes_apply {U V : X.Opens} (h : V ≤ U) (b : Fam T U) (i : ι) :
    famRes T h b i = X.presheaf.map (homOfLE (inf_le_inf_right (T i) h)).op (b i) := rfl

lemma famRes_smul {U V : X.Opens} (h : V ≤ U) (r : Γ(X, U)) (b : Fam T U) :
    famRes T h (r • b) = X.presheaf.map (homOfLE h).op r • famRes T h b := by
  funext i
  rw [famRes_apply, Fam.smul_apply, Fam.smul_apply, famRes_apply, map_mul, res_res, res_res]

/-- The abelian presheaf of families. -/
noncomputable def famPresheaf : TopCat.Presheaf Ab.{u} X where
  obj U := AddCommGrpCat.of (Fam T U.unop)
  map {U V} f := AddCommGrpCat.ofHom
    { toFun := famRes T (leOfHom f.unop)
      map_zero' := funext fun i ↦ by simp only [famRes_apply, Fam.zero_apply, map_zero]
      map_add' := fun b c ↦ funext fun i ↦ by
        simp only [famRes_apply, Fam.add_apply, map_add] }
  map_id U := by
    ext b
    funext i
    exact res_self _ (b i)
  map_comp f g := by
    ext b
    funext i
    exact (res_res _ _ (b i)).symm

instance (U : (X.Opens)ᵒᵖ) : Module (X.ringCatSheaf.obj.obj U) ((famPresheaf T).obj U) :=
  inferInstanceAs (Module Γ(X, U.unop) (Fam T U.unop))

/-- The presheaf of modules of families. -/
noncomputable def famModules : PresheafOfModules.{u} X.ringCatSheaf.obj :=
  PresheafOfModules.ofPresheaf (famPresheaf T) fun _ _ f r b ↦
    famRes_smul T (leOfHom f.unop) r b

/-- Families glue componentwise, since the structure sheaf is a sheaf. -/
lemma famPresheaf_isSheaf : (famPresheaf T).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat)]
  apply TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types
  intro κ U sf hsf
  have key : ∀ i, ∃! s : Γ(X, iSup U ⊓ T i), ∀ k,
      X.presheaf.map (homOfLE (inf_le_inf_right (T i) (le_iSup U k))).op s =
        (sf k : Fam T (U k)) i := by
    intro i
    refine X.sheaf.existsUnique_gluing' (fun k ↦ U k ⊓ T i) (iSup U ⊓ T i)
      (fun k ↦ homOfLE (inf_le_inf_right (T i) (le_iSup U k))) ?_
      (fun k ↦ (sf k : Fam T (U k)) i) ?_
    · intro x hx
      obtain ⟨k, hk⟩ := Opens.mem_iSup.mp hx.1
      exact Opens.mem_iSup.mpr ⟨k, hk, hx.2⟩
    · intro k l
      have h : X.presheaf.map (homOfLE (inf_le_inf_right (T i)
            (inf_le_left : U k ⊓ U l ≤ U k))).op ((sf k : Fam T (U k)) i) =
          X.presheaf.map (homOfLE (inf_le_inf_right (T i)
            (inf_le_right : U k ⊓ U l ≤ U l))).op ((sf l : Fam T (U l)) i) :=
        congrFun (hsf k l) i
      have hle : (U k ⊓ T i) ⊓ (U l ⊓ T i) ≤ (U k ⊓ U l) ⊓ T i :=
        le_inf (inf_le_inf inf_le_left inf_le_left) (inf_le_left.trans inf_le_right)
      have h' := congrArg (fun z ↦ X.presheaf.map (homOfLE hle).op z) h
      simp only [res_res] at h'
      exact h'
  choose s hs hu using key
  refine ⟨(s : Fam T (iSup U)), fun k ↦ funext fun i ↦ hs i k, fun s' hs' ↦ funext fun i ↦ ?_⟩
  exact hu i ((s' : Fam T (iSup U)) i) fun k ↦ congrFun (hs' k) i

/-- The sheaf of modules of families. -/
noncomputable def famSheaf : X.Modules where
  val := famModules T
  isSheaf := famPresheaf_isSheaf T

variable {T} (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ)

/-- The cocycle identity, in the form of the target statement. -/
def IsCocycle : Prop :=
  ∀ i j k : ι,
    X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ⊓ T k ≤ T i ⊓ T j)).op
        (g i j : Γ(X, T i ⊓ T j)) *
      X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        T i ⊓ T j ⊓ T k ≤ T j ⊓ T k)).op (g j k : Γ(X, T j ⊓ T k)) =
    X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        T i ⊓ T j ⊓ T k ≤ T i ⊓ T k)).op (g i k : Γ(X, T i ⊓ T k))

/-- The cocycle identity on any open inside a triple overlap. -/
lemma cocycle_res (hg : IsCocycle g) (i j k : ι) {W : X.Opens} (hij : W ≤ T i ⊓ T j)
    (hjk : W ≤ T j ⊓ T k) (hik : W ≤ T i ⊓ T k) :
    X.presheaf.map (homOfLE hij).op (g i j : Γ(X, T i ⊓ T j)) *
        X.presheaf.map (homOfLE hjk).op (g j k : Γ(X, T j ⊓ T k)) =
      X.presheaf.map (homOfLE hik).op (g i k : Γ(X, T i ⊓ T k)) := by
  have hW : W ≤ T i ⊓ T j ⊓ T k := le_inf hij (hjk.trans inf_le_right)
  have h := congrArg (fun z ↦ X.presheaf.map (homOfLE hW).op z) (hg i j k)
  simp only [map_mul, res_res] at h
  exact h

/-- The cocycle relation `b i = g i j * b j` on every open inside `U ⊓ T i ⊓ T j`. -/
def Compat {U : X.Opens} (b : Fam T U) : Prop :=
  ∀ (i j : ι) (V : X.Opens) (hi : V ≤ U ⊓ T i) (hj : V ≤ U ⊓ T j),
    X.presheaf.map (homOfLE hi).op (b i) =
      X.presheaf.map (homOfLE (le_inf (hi.trans inf_le_right) (hj.trans inf_le_right))).op
          (g i j : Γ(X, T i ⊓ T j)) * X.presheaf.map (homOfLE hj).op (b j)

lemma compat_zero {U : X.Opens} : Compat g (0 : Fam T U) := fun i j V hi hj ↦ by
  simp only [Fam.zero_apply, map_zero, mul_zero]

lemma compat_add {U : X.Opens} {b c : Fam T U} (hb : Compat g b) (hc : Compat g c) :
    Compat g (b + c) := fun i j V hi hj ↦ by
  rw [Fam.add_apply, Fam.add_apply, map_add, map_add, hb i j V hi hj, hc i j V hi hj, mul_add]

lemma compat_smul {U : X.Opens} (r : Γ(X, U)) {b : Fam T U} (hb : Compat g b) :
    Compat g (r • b) := fun i j V hi hj ↦ by
  rw [Fam.smul_apply, Fam.smul_apply, map_mul, map_mul, res_res, res_res, hb i j V hi hj]
  exact mul_left_comm _ _ _

lemma compat_res {U V : X.Opens} (h : V ≤ U) {b : Fam T U} (hb : Compat g b) :
    Compat g (famRes T h b) := fun i j W hi hj ↦ by
  rw [famRes_apply, famRes_apply, res_res, res_res]
  exact hb i j W (hi.trans (inf_le_inf_right _ h)) (hj.trans (inf_le_inf_right _ h))

/-- The sheaf submodule of families satisfying the cocycle relation. -/
noncomputable def gluedSubmodule : SheafOfModules.Submodule (famSheaf T) where
  obj U :=
    { carrier := {b | Compat g (b : Fam T U.unop)}
      add_mem' := fun hb hc ↦ compat_add g hb hc
      zero_mem' := compat_zero g
      smul_mem' := fun r _ hb ↦ compat_smul g r hb }
  map f _ hb := compat_res g (leOfHom f.unop) hb
  isSheaf U b hb := by
    intro i j V hi hj
    apply eq_of_local
    intro x hxV
    obtain ⟨W, f, hf, hxW⟩ := hb x (hi hxV).1
    have hWU : W ≤ U.unop := leOfHom f
    have hf' : Compat g (famRes T hWU (b : Fam T U.unop)) := hf
    refine ⟨V ⊓ W, inf_le_left, ⟨hxV, hxW⟩, ?_⟩
    have key := hf' i j (V ⊓ W) (le_inf inf_le_right ((inf_le_left.trans hi).trans inf_le_right))
      (le_inf inf_le_right ((inf_le_left.trans hj).trans inf_le_right))
    rw [famRes_apply, famRes_apply, res_res, res_res] at key
    rw [map_mul, res_res, res_res, res_res, key]

/-- The line bundle glued from the cocycle `g`. -/
noncomputable def glued : X.Modules := (gluedSubmodule g).toSheafOfModules

/-- A section of the glued sheaf from a family satisfying the cocycle relation. -/
def mk {U : X.Opens} (b : Fam T U) (hb : Compat g b) : Γ(glued g, U) := ⟨b, hb⟩

lemma mk_eq_mk {U : X.Opens} {b c : Fam T U} (hb : Compat g b) (hc : Compat g c) (h : b = c) :
    mk g b hb = mk g c hc := by
  subst h
  rfl

lemma map_mk {U V : X.Opens} (h : V ≤ U) (b : Fam T U) (hb : Compat g b) :
    (glued g).presheaf.map (homOfLE h).op (mk g b hb) = mk g (famRes T h b) (compat_res g h hb) :=
  rfl

lemma smul_mk {U : X.Opens} (r : Γ(X, U)) (b : Fam T U) (hb : Compat g b) :
    r • mk g b hb = mk g (r • b) (compat_smul g r hb) :=
  rfl

/-- The `i`-th component of a section of the glued sheaf. -/
def comp {U : X.Opens} (m : Γ(glued g, U)) (i : ι) : Γ(X, U ⊓ T i) := (m.1 : Fam T U) i

lemma comp_mk {U : X.Opens} (b : Fam T U) (hb : Compat g b) (i : ι) : comp g (mk g b hb) i = b i :=
  rfl

lemma eq_of_comp {U : X.Opens} {m m' : Γ(glued g, U)} (h : ∀ i, comp g m i = comp g m' i) :
    m = m' :=
  Subtype.ext (funext h)

lemma compat_of_mem {U : X.Opens} (m : Γ(glued g, U)) : Compat g (m.1 : Fam T U) := m.2

/-- The local generator over an open `V ≤ T i`: its `j`-th component is `g j i`. -/
def gen (i : ι) {V : X.Opens} (hV : V ≤ T i) : Fam T V :=
  fun j ↦ X.presheaf.map (homOfLE (le_inf inf_le_right (inf_le_left.trans hV) :
    V ⊓ T j ≤ T j ⊓ T i)).op (g j i : Γ(X, T j ⊓ T i))

lemma gen_apply (i : ι) {V : X.Opens} (hV : V ≤ T i) (j : ι) :
    gen g i hV j = X.presheaf.map (homOfLE (le_inf inf_le_right (inf_le_left.trans hV) :
      V ⊓ T j ≤ T j ⊓ T i)).op (g j i : Γ(X, T j ⊓ T i)) := rfl

lemma gen_compat (hg : IsCocycle g) (i : ι) {V : X.Opens} (hV : V ≤ T i) :
    Compat g (gen g i hV) := fun j k W hj hk ↦ by
  rw [gen_apply, gen_apply, res_res, res_res]
  exact (cocycle_res g hg j k i _ _ _).symm

lemma famRes_gen (i : ι) {U V : X.Opens} (h : V ≤ U) (hU : U ≤ T i) :
    famRes T h (gen g i hU) = gen g i (h.trans hU) := by
  funext j
  rw [famRes_apply, gen_apply, gen_apply, res_res]

/-- The local generator as a section of the glued sheaf. -/
noncomputable def genSec (hg : IsCocycle g) (i : ι) {V : X.Opens} (hV : V ≤ T i) :
    Γ(glued g, V) :=
  mk g (gen g i hV) (gen_compat g hg i hV)

lemma map_genSec (hg : IsCocycle g) (i : ι) {U V : X.Opens} (h : V ≤ U) (hU : U ≤ T i) :
    (glued g).presheaf.map (homOfLE h).op (genSec g hg i hU) = genSec g hg i (h.trans hU) :=
  mk_eq_mk g _ _ (famRes_gen g i h hU)

/-- Over an open inside `T i`, the glued sheaf is free on the local generator. -/
lemma smul_genSec_bijective (hg : IsCocycle g) (i : ι) {V : X.Opens} (hV : V ≤ T i) :
    Function.Bijective (fun r : Γ(X, V) ↦ r • genSec g hg i hV) := by
  have e : ∀ z : Γ(X, V), X.presheaf.map (homOfLE (le_inf le_rfl hV : V ≤ V ⊓ T i)).op
      (X.presheaf.map (homOfLE (inf_le_left : V ⊓ T i ≤ V)).op z) = z := fun z ↦ by
    rw [res_res, res_self]
  constructor
  · intro r s hrs
    have h : X.presheaf.map (homOfLE (inf_le_left : V ⊓ T i ≤ V)).op r * gen g i hV i =
        X.presheaf.map (homOfLE (inf_le_left : V ⊓ T i ≤ V)).op s * gen g i hV i :=
      congrArg (fun m ↦ comp g m i) hrs
    have hu : IsUnit (gen g i hV i) := by
      rw [gen_apply]
      exact (g i i).isUnit.map (X.presheaf.map _).hom
    rw [← e r, ← e s, hu.mul_left_injective h]
  · intro m
    refine ⟨X.presheaf.map (homOfLE (le_inf le_rfl hV : V ≤ V ⊓ T i)).op (comp g m i),
      eq_of_comp g fun j ↦ ?_⟩
    have h := compat_of_mem g m j i (V ⊓ T j) le_rfl (le_inf inf_le_left (inf_le_left.trans hV))
    rw [res_self] at h
    change X.presheaf.map (homOfLE (inf_le_left : V ⊓ T j ≤ V)).op
        (X.presheaf.map (homOfLE (le_inf le_rfl hV : V ≤ V ⊓ T i)).op (comp g m i)) *
          gen g i hV j = comp g m j
    rw [res_res, gen_apply, mul_comm]
    exact h.symm

/-- The glued sheaf is a line bundle. -/
lemma isLocallyFreeRankOne_glued (hT : (⨆ i, T i) = ⊤) (hg : IsCocycle g) :
    IsLocallyFreeRankOne (glued g) := by
  intro x
  have hx : x ∈ (⨆ i, T i) := by
    rw [hT]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  refine ⟨T i, hi, ⟨?_⟩⟩
  let N' := (glued g).restrict (T i).ι
  let s : GlobalSections N' := genSec g hg i ((T i).ι_image_le ⊤)
  have key : ∀ (W : (T i).toScheme.Opens) (a : Γ((T i).toScheme, W)),
      (sectionHom N' s).app W a =
        ((T i).ι.appIso W).inv a • genSec g hg i ((T i).ι_image_le W) := by
    intro W a
    have h1 : N'.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op s =
        genSec g hg i ((T i).ι_image_le W) :=
      map_genSec g hg i (((T i).ι.opensFunctor.map (homOfLE (le_top : W ≤ ⊤))).le) _
    rw [sectionHom_app, h1]
    rfl
  have : IsIso (sectionHom N' s) := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro W
    rw [ConcreteCategory.isIso_iff_bijective]
    have hb := smul_genSec_bijective g hg i ((T i).ι_image_le W)
    have hinv := ConcreteCategory.bijective_of_isIso ((T i).ι.appIso W).inv
    constructor
    · intro a a' h
      rw [key, key] at h
      exact hinv.1 (hb.1 h)
    · intro m
      obtain ⟨r, hr⟩ := hb.2 m
      obtain ⟨a, rfl⟩ := hinv.2 r
      exact ⟨a, (key W a).trans hr⟩
  exact (asIso (sectionHom N' s)).symm

/-- A family of functions compatible with the cocycle. -/
def IsCompatibleFamily (a : ∀ i : ι, Γ(X, T i)) : Prop :=
  ∀ i j : ι,
    X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (a i) =
      (g i j : Γ(X, T i ⊓ T j)) *
        X.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op (a j)

/-- The family underlying the global section defined by a compatible family. -/
def sec (a : ∀ i : ι, Γ(X, T i)) : Fam T ⊤ :=
  fun i ↦ X.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ T i ≤ T i)).op (a i)

lemma sec_compat {a : ∀ i : ι, Γ(X, T i)} (ha : IsCompatibleFamily g a) : Compat g (sec a) := by
  intro i j V hi hj
  have hV : V ≤ T i ⊓ T j := le_inf (hi.trans inf_le_right) (hj.trans inf_le_right)
  have h := congrArg (fun z ↦ X.presheaf.map (homOfLE hV).op z) (ha i j)
  simp only [map_mul, res_res] at h
  change X.presheaf.map (homOfLE hi).op (X.presheaf.map (homOfLE inf_le_right).op (a i)) =
    _ * X.presheaf.map (homOfLE hj).op (X.presheaf.map (homOfLE inf_le_right).op (a j))
  rw [res_res, res_res]
  exact h

/-- The global section of the glued sheaf defined by a compatible family. -/
noncomputable def globalSec {a : ∀ i : ι, Γ(X, T i)} (ha : IsCompatibleFamily g a) :
    GlobalSections (glued g) :=
  mk g (sec a) (sec_compat g ha)

/-- On an open inside `T i`, the global section is `a i` times the local generator. -/
lemma map_globalSec (hg : IsCocycle g) {a : ∀ i : ι, Γ(X, T i)} (ha : IsCompatibleFamily g a)
    (i : ι) {V : X.Opens} (hV : V ≤ T i) :
    (glued g).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op (globalSec g ha) =
      X.presheaf.map (homOfLE hV).op (a i) • genSec g hg i hV := by
  apply eq_of_comp g
  intro j
  have hle : V ⊓ T j ≤ T j ⊓ T i := le_inf inf_le_right (inf_le_left.trans hV)
  have h := congrArg (fun z ↦ X.presheaf.map (homOfLE hle).op z) (ha j i)
  simp only [map_mul, res_res] at h
  change X.presheaf.map (homOfLE (inf_le_inf_right (T j) (show V ≤ ⊤ from le_top))).op
      (X.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ T j ≤ T j)).op (a j)) =
    X.presheaf.map (homOfLE (inf_le_left : V ⊓ T j ≤ V)).op
      (X.presheaf.map (homOfLE hV).op (a i)) * gen g i hV j
  rw [res_res, res_res, gen_apply, h, mul_comm]

/-- The generation open of the global section meets `T i` in the basic open of `a i`. -/
theorem inf_trivializationOpen_globalSec (hg : IsCocycle g) {a : ∀ i : ι, Γ(X, T i)}
    (ha : IsCompatibleFamily g a) (i : ι) :
    T i ⊓ trivializationOpen (glued g) (globalSec g ha) = X.basicOpen (a i) := by
  apply le_antisymm
  · rintro x ⟨hxi, hxs⟩
    obtain ⟨U, hU, hxU⟩ := Opens.mem_sSup.mp hxs
    have hbij := (trivializesOn_iff_bijective (glued g) _ U).mp hU (U ⊓ T i) inf_le_left
    obtain ⟨r, hr⟩ := hbij.2 (genSec g hg i (inf_le_right : U ⊓ T i ≤ T i))
    rw [sectionHom_app, map_globalSec g hg ha i inf_le_right, smul_smul] at hr
    have h1 : (show Γ(X, U ⊓ T i) from r) *
        X.presheaf.map (homOfLE (inf_le_right : U ⊓ T i ≤ T i)).op (a i) = 1 :=
      (smul_genSec_bijective g hg i inf_le_right).1 (hr.trans (one_smul _ _).symm)
    have hu := IsUnit.of_mul_eq_one_right _ h1
    have hB := X.basicOpen_of_isUnit hu
    rw [Scheme.basicOpen_res] at hB
    have hx : x ∈ U ⊓ T i := ⟨hxU, hxi⟩
    rw [← hB] at hx
    exact hx.2
  · intro x hx
    have hB : TrivializesOn (glued g) (globalSec g ha) (X.basicOpen (a i)) := by
      rw [trivializesOn_iff_bijective]
      intro W hW
      have hWi : W ≤ T i := hW.trans (X.basicOpen_le _)
      have hu : IsUnit (X.presheaf.map (homOfLE hWi).op (a i)) := by
        rw [← res_res (X.basicOpen_le (a i)) hW]
        exact (X.toRingedSpace.isUnit_res_basicOpen (a i)).map
          (X.presheaf.map (homOfLE hW).op).hom
      have key : ∀ r : Γ(X, W), (sectionHom (glued g) (globalSec g ha)).app W r =
          (r * X.presheaf.map (homOfLE hWi).op (a i)) • genSec g hg i hWi := fun r ↦ by
        rw [sectionHom_app, map_globalSec g hg ha i hWi, smul_smul]
      have hb := smul_genSec_bijective g hg i hWi
      constructor
      · intro r r' h
        rw [key, key] at h
        exact hu.mul_left_injective (hb.1 h)
      · intro m
        obtain ⟨r, hr⟩ := hb.2 m
        refine ⟨r * ((hu.unit⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)), ?_⟩
        rw [key, mul_assoc, IsUnit.val_inv_mul, mul_one]
        exact hr
    have hle : X.basicOpen (a i) ≤ trivializationOpen (glued g) (globalSec g ha) := le_sSup hB
    exact ⟨X.basicOpen_le (a i) hx, hle hx⟩

end Langlands.AlgebraicGeometry.Picard.CocycleGluing

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule

/-- The line bundle glued from a unit cocycle on an open cover: every family of functions
compatible with the cocycle gives a global section whose generation open meets each `T i`
in the basic open of the `i`-th function. -/
theorem exists_cocycleLineBundle {X : Scheme.{u}} {ι : Type u} (T : ι → X.Opens)
    (hT : (⨆ i, T i) = ⊤) (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ)
    (hg : ∀ i j k : ι,
      X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ⊓ T k ≤ T i ⊓ T j)).op
          (g i j : Γ(X, T i ⊓ T j)) *
        X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          T i ⊓ T j ⊓ T k ≤ T j ⊓ T k)).op (g j k : Γ(X, T j ⊓ T k)) =
      X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          T i ⊓ T j ⊓ T k ≤ T i ⊓ T k)).op (g i k : Γ(X, T i ⊓ T k))) :
    ∃ N : LineBundle X, ∀ a : ∀ i : ι, Γ(X, T i),
      (∀ i j : ι,
        X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (a i) =
          (g i j : Γ(X, T i ⊓ T j)) *
            X.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op (a j)) →
      ∃ t : GlobalSections N.obj, ∀ i : ι,
        T i ⊓ trivializationOpen N.obj t = X.basicOpen (a i) :=
  ⟨⟨CocycleGluing.glued g, CocycleGluing.isLocallyFreeRankOne_glued g hT hg⟩, fun _ ha ↦
    ⟨CocycleGluing.globalSec g ha, CocycleGluing.inf_trivializationOpen_globalSec g hg ha⟩⟩

/-- Proof of the cocycle line bundle statement. -/
theorem cocycleLineBundle : CocycleLineBundleStatement.{u} :=
  fun _ _ T hT g hg ↦ exists_cocycleLineBundle T hT g hg

end Langlands.AlgebraicGeometry.Picard
