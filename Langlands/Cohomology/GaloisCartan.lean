import Langlands.Cohomology.RightDerivedSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-! # A Galois–Cartan criterion for higher right derived functors -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Cohomology.GaloisCartan

open CategoryTheory CategoryTheory.Limits

universe u v w a b

variable {D : Type u} [Category.{v} D]
variable {R : Type w} [CommRing R]

/-- A left action of a group `Γ` on a functor `T` to modules by natural endomorphisms:
`act (γ * δ)` is `act δ` followed by `act γ`. -/
structure NaturalAction (Γ : Type w) [Group Γ] (T : D ⥤ ModuleCat.{w} R) where
  act : Γ → (T ⟶ T)
  act_one : act 1 = 𝟙 T
  act_mul : ∀ γ δ : Γ, act (γ * δ) = act δ ≫ act γ

namespace NaturalAction

variable {Γ : Type w} [Group Γ] {T : D ⥤ ModuleCat.{w} R} (A : NaturalAction Γ T)

/-- The representation of `Γ` on the values of `T` at `F`. -/
def representation (F : D) : Representation R Γ (T.obj F) where
  toFun γ := ((A.act γ).app F).hom
  map_one' := by rw [A.act_one]; rfl
  map_mul' γ δ := by rw [A.act_mul]; rfl

@[simp]
theorem representation_apply (F : D) (γ : Γ) (x : T.obj F) :
    A.representation F γ x = (A.act γ).app F x := rfl

/-- The value of `T` at `F` as a representation of `Γ`. -/
abbrev rep (F : D) : Rep.{w} R Γ := Rep.of (A.representation F)

theorem act_naturality_apply {F F' : D} (g : F ⟶ F') (γ : Γ) (x : T.obj F) :
    T.map g ((A.act γ).app F x) = (A.act γ).app F' (T.map g x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, (A.act γ).naturality]

/-- The equivariant map of representations induced by a morphism. -/
def repMap {F F' : D} (g : F ⟶ F') : A.rep F ⟶ A.rep F' :=
  Rep.ofHom ⟨(T.map g).hom, fun γ => by
    ext x
    exact A.act_naturality_apply g γ x⟩

@[simp]
theorem repMap_hom_apply {F F' : D} (g : F ⟶ F') (x : T.obj F) :
    (A.repMap g).hom x = T.map g x := rfl

end NaturalAction

variable [Abelian D]

/-- A Galois–Čech system for a family of functors `T i` to modules. Each index `i` has
covers `c`. A cover has a group `group i c`, a target index `target i c` and a natural
action of the group on `T (target i c)`. The augmentation `aug i c : T i ⟶ T (target i c)`
identifies `T i` with the invariants of the action. Every element of `T i` at the
quotient of a short exact sequence lifts to the middle term after augmentation to some
cover. On injective objects the group cohomology of the target modules vanishes in
positive degrees. -/
structure GaloisCechSystem {ι : Type a} (T : ι → D ⥤ ModuleCat.{w} R) where
  Cover : ι → Type b
  group : ∀ i, Cover i → Type w
  [instGroup : ∀ i c, Group (group i c)]
  target : ∀ i, Cover i → ι
  action : ∀ i c, NaturalAction (group i c) (T (target i c))
  aug : ∀ i c, T i ⟶ T (target i c)
  aug_injective : ∀ i c (F : D), Function.Injective ((aug i c).app F)
  aug_act : ∀ i c (γ : group i c), aug i c ≫ (action i c).act γ = aug i c
  exists_aug_eq : ∀ i c (F : D) (x : (T (target i c)).obj F),
    (∀ γ : group i c, ((action i c).act γ).app F x = x) → ∃ s, (aug i c).app F s = x
  local_lift : ∀ (S : ShortComplex D), S.ShortExact → ∀ i (s : (T i).obj S.X₃),
    ∃ (c : Cover i) (t : (T (target i c)).obj S.X₂),
      (T (target i c)).map S.g t = (aug i c).app S.X₃ s
  injective_acyclic : ∀ i c (I : D) [Injective I] (n : ℕ),
    IsZero (groupCohomology ((action i c).rep I) (n + 1))

attribute [instance] GaloisCechSystem.instGroup

namespace GaloisCechSystem

variable {ι : Type a} {T : ι → D ⥤ ModuleCat.{w} R} (K : GaloisCechSystem.{u, v, w, a, b} T)

/-- Positive-degree group cohomology of all the cover modules of `F` vanishes. -/
def GaloisAcyclic (F : D) : Prop :=
  ∀ i c (n : ℕ), IsZero (groupCohomology ((K.action i c).rep F) (n + 1))

/-- Injective objects are Galois acyclic. -/
theorem galoisAcyclic_of_injective (I : D) [Injective I] : K.GaloisAcyclic I :=
  fun i c n => K.injective_acyclic i c I n

variable [∀ i, (T i).Additive] [∀ i, PreservesFiniteLimits (T i)]

omit [∀ i, PreservesFiniteLimits (T i)] in
theorem map_f_map_g_apply (S : ShortComplex D) (j : ι) (x : (T j).obj S.X₁) :
    (T j).map S.g ((T j).map S.f x) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, S.zero, Functor.map_zero]
  rfl

omit [∀ i, (T i).Additive] in
theorem map_f_injective (S : ShortComplex D) (hS : S.ShortExact) (j : ι) :
    Function.Injective ((T j).map S.f) := by
  have := hS.mono_f
  exact (ModuleCat.mono_iff_injective _).1 inferInstance

theorem exists_map_f_eq (S : ShortComplex D) (hS : S.ShortExact) (j : ι)
    (y : (T j).obj S.X₂) (hy : (T j).map S.g y = 0) :
    ∃ x : (T j).obj S.X₁, (T j).map S.f x = y := by
  have := hS.mono_f
  have hex : (S.map (T j)).Exact :=
    hS.exact.map_of_mono_of_preservesKernel (T j) inferInstance inferInstance
  exact (ShortComplex.moduleCat_exact_iff _).1 hex y hy

omit [∀ i, (T i).Additive] [∀ i, PreservesFiniteLimits (T i)] in
theorem aug_naturality_apply (i : ι) (c : K.Cover i) {F F' : D} (g : F ⟶ F')
    (x : (T i).obj F) :
    (K.aug i c).app F' ((T i).map g x) = (T (K.target i c)).map g ((K.aug i c).app F x) := by
  rw [← ConcreteCategory.comp_apply, (K.aug i c).naturality, ConcreteCategory.comp_apply]

/-- If the first term of a short exact sequence is Galois acyclic, every `T i` is
surjective on the second arrow. The local lift is corrected by a degree-one cocycle,
which is a coboundary, and the corrected lift descends to `T i`. -/
theorem surjective_map_g (S : ShortComplex D) (hS : S.ShortExact)
    (hF : K.GaloisAcyclic S.X₁) (i : ι) :
    Function.Surjective ((T i).map S.g) := by
  intro s
  obtain ⟨c, t, ht⟩ := K.local_lift S hS i s
  have hcoc : ∀ γ : K.group i c,
      (T (K.target i c)).map S.g (((K.action i c).act γ).app S.X₂ t - t) = 0 := by
    intro γ
    rw [map_sub, (K.action i c).act_naturality_apply, ht, ← ConcreteCategory.comp_apply,
      ← NatTrans.comp_app, K.aug_act, sub_self]
  choose ψ hψ using fun γ => exists_map_f_eq (T := T) S hS (K.target i c) _ (hcoc γ)
  have hψmem : ψ ∈ groupCohomology.cocycles₁ ((K.action i c).rep S.X₁) := by
    rw [groupCohomology.mem_cocycles₁_iff]
    intro γ δ
    apply map_f_injective (T := T) S hS (K.target i c)
    change (T (K.target i c)).map S.f (ψ (γ * δ)) =
      (T (K.target i c)).map S.f (((K.action i c).act γ).app S.X₁ (ψ δ) + ψ γ)
    rw [map_add, (K.action i c).act_naturality_apply, hψ, hψ, hψ, (K.action i c).act_mul,
      NatTrans.comp_app, ConcreteCategory.comp_apply, map_sub]
    abel
  have h0 : groupCohomology.H1π ((K.action i c).rep S.X₁) = 0 := (hF i c 0).eq_of_tgt _ _
  have hzero : groupCohomology.H1π ((K.action i c).rep S.X₁) ⟨ψ, hψmem⟩ = 0 := by
    rw [h0]
    rfl
  obtain ⟨b, hb⟩ := (groupCohomology.H1π_eq_zero_iff _).1 hzero
  have hψb : ∀ γ, ψ γ = ((K.action i c).act γ).app S.X₁ b - b := fun γ =>
    (congrFun hb γ).symm
  have hinv : ∀ γ : K.group i c, ((K.action i c).act γ).app S.X₂
      (t - (T (K.target i c)).map S.f b) = t - (T (K.target i c)).map S.f b := by
    intro γ
    have h1 := hψ γ
    rw [hψb, map_sub, eq_sub_iff_add_eq] at h1
    rw [map_sub, ← (K.action i c).act_naturality_apply, ← h1]
    abel
  obtain ⟨u, hu⟩ := K.exists_aug_eq i c S.X₂ _ hinv
  refine ⟨u, K.aug_injective i c S.X₃ ?_⟩
  rw [K.aug_naturality_apply, hu, map_sub, map_f_map_g_apply (T := T), sub_zero, ht]

/-- The short complex of representations induced by a short complex of `D`. -/
def repShortComplex (i : ι) (c : K.Cover i) (S : ShortComplex D) :
    ShortComplex (Rep.{w} R (K.group i c)) :=
  ShortComplex.mk ((K.action i c).repMap S.f) ((K.action i c).repMap S.g) (by
    ext x
    exact map_f_map_g_apply (T := T) S (K.target i c) x)

/-- A short exact sequence whose first term is Galois acyclic induces short exact
sequences of cover representations. -/
theorem repShortComplex_shortExact (S : ShortComplex D) (hS : S.ShortExact)
    (hF : K.GaloisAcyclic S.X₁) (i : ι) (c : K.Cover i) :
    (K.repShortComplex i c S).ShortExact where
  exact := (forget₂ (Rep.{w} R (K.group i c)) (ModuleCat R)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2 fun x hx =>
      exists_map_f_eq (T := T) S hS (K.target i c) x hx
  mono_f := (Rep.mono_iff_injective _).2 (map_f_injective (T := T) S hS (K.target i c))
  epi_g := (Rep.epi_iff_surjective _).2 (K.surjective_map_g S hS hF (K.target i c))

/-- Galois acyclicity passes to the quotient of a Galois-acyclic object by an embedding
into an injective object. -/
theorem galoisAcyclic_quotient (S : ShortComplex D) (hS : S.ShortExact) [Injective S.X₂]
    (hF : K.GaloisAcyclic S.X₁) : K.GaloisAcyclic S.X₃ := by
  intro i c n
  have hX := K.repShortComplex_shortExact S hS hF i c
  have hex := groupCohomology.mapShortComplex₃_exact hX (i := n + 1) (j := n + 1 + 1) rfl
  exact hex.isZero_X₂ ((K.injective_acyclic i c S.X₂ n).eq_of_src _ _)
    ((hF i c (n + 1)).eq_of_tgt _ _)

variable [EnoughInjectives D]

/-- **Galois–Cartan criterion.** Every higher right derived functor of every `T i`
vanishes on a Galois-acyclic object. -/
theorem isZero_rightDerived_of_galoisAcyclic (F : D) (hF : K.GaloisAcyclic F) (i : ι)
    (n : ℕ) : IsZero (((T i).rightDerived (n + 1)).obj F) := by
  let := HasDerivedCategory.standard D
  let := HasDerivedCategory.standard (ModuleCat.{w} R)
  induction n generalizing F with
  | zero =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
      (cokernel.condition _)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk'
        (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
        inferInstance inferInstance
    have : Epi ((T i).map S.g) :=
      (ModuleCat.epi_iff_surjective _).2 (K.surjective_map_g S hS hF i)
    have he : ((T i).rightDerived 0).map S.g =
        (T i).rightDerivedZeroIsoSelf.hom.app S.X₂ ≫ (T i).map S.g ≫
          (T i).rightDerivedZeroIsoSelf.inv.app S.X₃ := by
      rw [← Category.assoc, ← (T i).rightDerivedZeroIsoSelf.hom.naturality,
        Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    have : Epi (((T i).rightDerived 0).map S.g) := by
      rw [he]
      infer_instance
    have : Epi (DerivedPlus.rightDerivedδ (T i) hS 0 1 rfl) :=
      DerivedPlus.epi_rightDerivedδ_of_isZero (T i) hS 0 1 rfl
        ((T i).isZero_rightDerived_obj_injective_succ 0 (Injective.under F))
    exact IsZero.of_epi_eq_zero _ (zero_of_epi_comp _
      (DerivedPlus.rightDerived_map_comp_δ (T i) hS 0 1 rfl))
  | succ n ih =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
      (cokernel.condition _)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk'
        (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
        inferInstance inferInstance
    have hQ := K.galoisAcyclic_quotient S hS hF
    have : Epi (DerivedPlus.rightDerivedδ (T i) hS (n + 1) (n + 1 + 1) rfl) :=
      DerivedPlus.epi_rightDerivedδ_of_isZero (T i) hS _ _ rfl
        ((T i).isZero_rightDerived_obj_injective_succ (n + 1) (Injective.under F))
    exact IsZero.of_epi (DerivedPlus.rightDerivedδ (T i) hS (n + 1) (n + 1 + 1) rfl)
      (ih S.X₃ hQ)

omit [∀ i, (T i).Additive] [∀ i, PreservesFiniteLimits (T i)] in
/-- Isomorphic additive functors have isomorphic right derived functors. -/
def rightDerivedIsoOfIso {T₁ T₂ : D ⥤ ModuleCat.{w} R} [T₁.Additive] [T₂.Additive]
    (e : T₁ ≅ T₂) (q : ℕ) : T₁.rightDerived q ≅ T₂.rightDerived q where
  hom := NatTrans.rightDerived e.hom q
  inv := NatTrans.rightDerived e.inv q
  hom_inv_id := by
    rw [← NatTrans.rightDerived_comp, Iso.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by
    rw [← NatTrans.rightDerived_comp, Iso.inv_hom_id, NatTrans.rightDerived_id]

/-- The criterion for an additive functor isomorphic to one of the `T i`. -/
theorem isZero_rightDerived_of_iso {T' : D ⥤ ModuleCat.{w} R} [T'.Additive] (i : ι)
    (e : T' ≅ T i) (F : D) (hF : K.GaloisAcyclic F) (n : ℕ) :
    IsZero ((T'.rightDerived (n + 1)).obj F) :=
  (K.isZero_rightDerived_of_galoisAcyclic F hF i n).of_iso
    ((rightDerivedIsoOfIso e (n + 1)).app F)

end GaloisCechSystem

end Langlands.Cohomology.GaloisCartan
