import Langlands.Sheaf.Equivariant.Smooth
import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.Tactic.Group

/-!
# The smooth part of an equivariant sheaf

When every neighbourhood of every point contains an open neighbourhood stable
under an open subgroup, the sections that are locally fixed by open subgroups
at every point form an equivariant subsheaf. It is smooth, and it is the
largest smooth subsheaf: the smooth part is right adjoint to the inclusion of
smooth equivariant module sheaves.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Pointwise

universe u uG

section Neighbourhoods

variable (G : Type uG) [Group G] [TopologicalSpace G]
variable (X : Type u) [TopologicalSpace X] [MulAction G X]

/-- Every open neighbourhood of every point contains an open neighbourhood of
that point which is stable under some open subgroup. -/
class HasStableNeighbourhoods : Prop where
  exists_stable : ∀ (x : X) (O : Set X), IsOpen O → x ∈ O →
    ∃ (H : OpenSubgroup G) (V : Set X), IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧
      ∀ h ∈ H, ∀ y ∈ V, h • y ∈ V

/-- For a discrete group the trivial subgroup is open and stabilizes every open. -/
instance (priority := 100) hasStableNeighbourhoods_of_discreteTopology [DiscreteTopology G] :
    HasStableNeighbourhoods G X where
  exists_stable x O hO hx := by
    refine ⟨⟨⊥, isOpen_discrete _⟩, O, hO, hx, subset_rfl, ?_⟩
    intro h hh y hy
    have h1 : h = 1 := Subgroup.mem_bot.1 hh
    subst h1
    simpa using hy

/-- For a continuous action of a nonarchimedean group, an open subgroup `H`
with `H • W ⊆ O` for an open `W ∋ x` gives the stable open `H • W`. -/
instance (priority := 100) hasStableNeighbourhoods_of_nonarchimedeanGroup
    [NonarchimedeanGroup G] [ContinuousSMul G X] : HasStableNeighbourhoods G X where
  exists_stable x O hO hx := by
    have hmem : (fun p : G × X => p.1 • p.2) ⁻¹' O ∈ nhds ((1 : G), x) :=
      continuous_smul.continuousAt.preimage_mem_nhds (by simpa using hO.mem_nhds hx)
    rw [nhds_prod_eq] at hmem
    obtain ⟨N, hN, W, hW, hNW⟩ := Filter.mem_prod_iff.1 hmem
    obtain ⟨H, hH⟩ := NonarchimedeanGroup.is_nonarchimedean N hN
    obtain ⟨W₀, hW₀W, hW₀, hxW₀⟩ := mem_nhds_iff.1 hW
    refine ⟨H, ⋃ h : (H : Subgroup G), (h : G) • W₀,
      isOpen_iUnion fun h => hW₀.smul _, ?_, ?_, ?_⟩
    · exact Set.mem_iUnion.2 ⟨1, ⟨x, hxW₀, one_smul G x⟩⟩
    · intro y hy
      obtain ⟨h, w, hw, rfl⟩ := Set.mem_iUnion.1 hy
      exact hNW (Set.mk_mem_prod (hH h.2) (hW₀W hw))
    · intro k hk y hy
      obtain ⟨h, w, hw, rfl⟩ := Set.mem_iUnion.1 hy
      refine Set.mem_iUnion.2 ⟨⟨k, hk⟩ * h, ⟨w, hw, ?_⟩⟩
      simp [mul_smul]

end Neighbourhoods

section Fixing

variable (R : Type u) [CommRing R]
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {X : Type u} [TopologicalSpace X] [MulAction G X]

omit [TopologicalSpace G] in
/-- Transport of fixed sections. If `H` fixes `t` over `V`, then the image of
`t` under a transport arrow `f : W ⟶ V` is fixed by every subgroup `H'`
stabilizing `W` whose conjugate by the label of `f` lies in `H`. -/
theorem map_invariantArrow_map_eq (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R)
    {V W : ActionOpens G X} (f : W ⟶ V) (H H' : Subgroup G)
    (hV : ∀ h : H, ∀ y ∈ V.openSet, (h : G) • y ∈ V.openSet)
    (hW : ∀ h : H', ∀ y ∈ W.openSet, (h : G) • y ∈ W.openSet)
    (hconj : ∀ h ∈ H', f.label * h * f.label⁻¹ ∈ H)
    (t : F.obj (op V))
    (ht : ∀ h : H, (F.map (ActionOpens.invariantArrow H V hV h).op).hom t = t) (h : H') :
    (F.map (ActionOpens.invariantArrow H' W hW h).op).hom ((F.map f.op).hom t) =
      (F.map f.op).hom t := by
  have harrow : ActionOpens.invariantArrow H' W hW h ≫ f =
      f ≫ ActionOpens.invariantArrow H V hV ⟨f.label * h * f.label⁻¹, hconj h h.2⟩ := by
    apply ActionOpens.Hom.ext
    simp only [ActionOpens.comp_label, ActionOpens.invariantArrow]
    group
  have key := congrArg (fun k => (F.map k.op).hom t) harrow
  simp only [op_comp, CategoryTheory.Functor.map_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply] at key
  rw [key, ht]

omit [TopologicalSpace G] in
/-- Restricting twice along label-one inclusions is restricting once. -/
theorem map_inclusionHom_map_inclusionHom (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R)
    {U V W : ActionOpens G X} (hWV : W.openSet ≤ V.openSet) (hVU : V.openSet ≤ U.openSet)
    (s : F.obj (op U)) :
    (F.map (ActionOpens.inclusionHom hWV).op).hom
        ((F.map (ActionOpens.inclusionHom hVU).op).hom s) =
      (F.map (ActionOpens.inclusionHom (hWV.trans hVU)).op).hom s := by
  have e : ActionOpens.inclusionHom hWV ≫ ActionOpens.inclusionHom hVU =
      ActionOpens.inclusionHom (hWV.trans hVU) :=
    ActionOpens.Hom.ext (by simp [ActionOpens.inclusionHom])
  have key := congrArg (fun k => (F.map k.op).hom s) e
  simpa only [op_comp, CategoryTheory.Functor.map_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply] using key

/-- Local fixedness at a point only depends on the restriction to a smaller
open containing the point. -/
theorem IsLocallyFixedAt.of_restrict {F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R}
    {U W : ActionOpens G X} (hWU : W.openSet ≤ U.openSet) {s : F.obj (op U)} {x : X}
    (hs : IsLocallyFixedAt R F ((F.map (ActionOpens.inclusionHom hWU).op).hom s) x) :
    IsLocallyFixedAt R F s x := by
  obtain ⟨V, hVW, H, hV, hxV, hfix⟩ := hs
  have hres := map_inclusionHom_map_inclusionHom R F hVW hWU s
  refine ⟨V, hVW.trans hWU, H, hV, hxV, fun h => ?_⟩
  rw [← hres]
  exact hfix h

/-- Images of locally fixed sections under morphisms of transport presheaves
are locally fixed. -/
theorem IsLocallyFixedAt.map {F F' : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R} (φ : F ⟶ F')
    {U : ActionOpens G X} {s : F.obj (op U)} {x : X} (hs : IsLocallyFixedAt R F s x) :
    IsLocallyFixedAt R F' ((φ.app (op U)).hom s) x := by
  obtain ⟨V, hVU, H, hV, hxV, hfix⟩ := hs
  refine ⟨V, hVU, H, hV, hxV, fun h => ?_⟩
  have h1 := congrArg (fun k => k.hom s) (φ.naturality (ActionOpens.inclusionHom hVU).op)
  have h2 := congrArg (fun k => k.hom ((F.map (ActionOpens.inclusionHom hVU).op).hom s))
    (φ.naturality (ActionOpens.invariantArrow (H : Subgroup G) V hV h).op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
  rw [← h1, ← h2, hfix h]

/-- Scalar multiples of locally fixed sections are locally fixed. -/
theorem IsLocallyFixedAt.smul {F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R}
    {U : ActionOpens G X} {s : F.obj (op U)} {x : X} (hs : IsLocallyFixedAt R F s x) (r : R) :
    IsLocallyFixedAt R F (r • s) x := by
  obtain ⟨V, hVU, H, hV, hxV, hfix⟩ := hs
  refine ⟨V, hVU, H, hV, hxV, fun h => ?_⟩
  rw [map_smul, map_smul, hfix h]

variable [IsTopologicalGroup G] [ContinuousConstSMul G X] [HasStableNeighbourhoods G X]

/-- Transport arrows preserve local fixedness: if `s` is locally fixed at the
translate of `x` by the label of `f`, then its image under `f` is locally fixed
at `x`. A smaller neighbourhood stable under a smaller open subgroup is chosen
inside the transported neighbourhood. -/
theorem IsLocallyFixedAt.map_arrow {F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R}
    {U W : ActionOpens G X} (f : W ⟶ U) {s : F.obj (op U)} {x : X}
    (hx : x ∈ W.openSet) (hs : IsLocallyFixedAt R F s (f.label • x)) :
    IsLocallyFixedAt R F ((F.map f.op).hom s) x := by
  obtain ⟨V, hVU, H, hV, hgx, hfix⟩ := hs
  have hO : IsOpen ((W.openSet : Set X) ∩ (fun y => f.label • y) ⁻¹' (V.openSet : Set X)) :=
    W.openSet.isOpen.inter (V.openSet.isOpen.preimage (continuous_const_smul f.label))
  obtain ⟨H₁, V₁, hV₁, hxV₁, hV₁O, hH₁⟩ :=
    HasStableNeighbourhoods.exists_stable (G := G) x _ hO ⟨hx, hgx⟩
  have hcont : Continuous (MulAut.conj f.label).toMonoidHom := by
    change Continuous fun k : G => f.label * k * f.label⁻¹
    fun_prop
  let K : OpenSubgroup G := H₁ ⊓ OpenSubgroup.comap (MulAut.conj f.label).toMonoidHom hcont H
  let V' : ActionOpens G X := ⟨⟨V₁, hV₁⟩⟩
  have hV'W : V'.openSet ≤ W.openSet := fun y hy => (hV₁O hy).1
  have hV' : ∀ k : (K : Subgroup G), ∀ y ∈ V'.openSet, (k : G) • y ∈ V'.openSet :=
    fun k y hy => hH₁ k (OpenSubgroup.mem_inf.1 k.2).1 y hy
  let ψ : V' ⟶ V := ⟨f.label, fun y hy => (hV₁O hy).2⟩
  refine ⟨V', hV'W, K, hV', hxV₁, fun k => ?_⟩
  have harrow : ActionOpens.inclusionHom hV'W ≫ f = ψ ≫ ActionOpens.inclusionHom hVU := by
    apply ActionOpens.Hom.ext
    simp [ActionOpens.inclusionHom, ψ]
  have hres := congrArg (fun k => (F.map k.op).hom s) harrow
  simp only [op_comp, CategoryTheory.Functor.map_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply] at hres
  rw [hres]
  exact map_invariantArrow_map_eq R F ψ H K hV hV'
    (fun k hk => OpenSubgroup.mem_comap.1 (OpenSubgroup.mem_inf.1 hk).2) _ hfix k

/-- Restriction to a smaller open containing the point preserves local fixedness. -/
theorem IsLocallyFixedAt.restrict {F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R}
    {U W : ActionOpens G X} (hWU : W.openSet ≤ U.openSet) {s : F.obj (op U)} {x : X}
    (hx : x ∈ W.openSet) (hs : IsLocallyFixedAt R F s x) :
    IsLocallyFixedAt R F ((F.map (ActionOpens.inclusionHom hWU).op).hom s) x :=
  IsLocallyFixedAt.map_arrow R (ActionOpens.inclusionHom hWU) hx (by
    simpa [ActionOpens.inclusionHom] using hs)

omit [IsTopologicalGroup G] [ContinuousConstSMul G X] in
/-- The zero section is locally fixed at every point of its open. -/
theorem isLocallyFixedAt_zero (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R)
    {U : ActionOpens G X} {x : X} (hx : x ∈ U.openSet) :
    IsLocallyFixedAt R F (0 : F.obj (op U)) x := by
  obtain ⟨H, V, hV, hxV, hVU, hH⟩ :=
    HasStableNeighbourhoods.exists_stable (G := G) x _ U.openSet.isOpen hx
  refine ⟨⟨⟨V, hV⟩⟩, hVU, H, fun h y hy => hH h h.2 y hy, hxV, fun h => ?_⟩
  simp only [map_zero]

omit [IsTopologicalGroup G] [ContinuousConstSMul G X] in
/-- Two sections locally fixed at the same point, possibly of different
presheaves, are fixed on a common smaller stable neighbourhood by a common open
subgroup: the intersection of the two subgroups with one stabilizing a small
neighbourhood inside both witnesses. -/
theorem IsLocallyFixedAt.exists_common {F₁ F₂ : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R}
    {U₁ U₂ : ActionOpens G X} {s₁ : F₁.obj (op U₁)} {s₂ : F₂.obj (op U₂)} {x : X}
    (hs₁ : IsLocallyFixedAt R F₁ s₁ x) (hs₂ : IsLocallyFixedAt R F₂ s₂ x) :
    ∃ (V : ActionOpens G X) (hV₁ : V.openSet ≤ U₁.openSet) (hV₂ : V.openSet ≤ U₂.openSet)
      (K : OpenSubgroup G)
      (hV : ∀ k : (K : Subgroup G), ∀ y ∈ V.openSet, (k : G) • y ∈ V.openSet),
      x ∈ V.openSet ∧
      (∀ k : (K : Subgroup G),
        (F₁.map (ActionOpens.invariantArrow (K : Subgroup G) V hV k).op).hom
            ((F₁.map (ActionOpens.inclusionHom hV₁).op).hom s₁) =
          (F₁.map (ActionOpens.inclusionHom hV₁).op).hom s₁) ∧
      (∀ k : (K : Subgroup G),
        (F₂.map (ActionOpens.invariantArrow (K : Subgroup G) V hV k).op).hom
            ((F₂.map (ActionOpens.inclusionHom hV₂).op).hom s₂) =
          (F₂.map (ActionOpens.inclusionHom hV₂).op).hom s₂) := by
  obtain ⟨V₁, hV₁U, H₁, hV₁, hxV₁, hfix₁⟩ := hs₁
  obtain ⟨V₂, hV₂U, H₂, hV₂, hxV₂, hfix₂⟩ := hs₂
  obtain ⟨H₃, V₃, hV₃, hxV₃, hV₃O, hH₃⟩ :=
    HasStableNeighbourhoods.exists_stable (G := G) x _
      (V₁.openSet.isOpen.inter V₂.openSet.isOpen) ⟨hxV₁, hxV₂⟩
  let K : OpenSubgroup G := H₁ ⊓ H₂ ⊓ H₃
  let V : ActionOpens G X := ⟨⟨V₃, hV₃⟩⟩
  have hV₁' : V.openSet ≤ V₁.openSet := fun y hy => (hV₃O hy).1
  have hV₂' : V.openSet ≤ V₂.openSet := fun y hy => (hV₃O hy).2
  have hV : ∀ k : (K : Subgroup G), ∀ y ∈ V.openSet, (k : G) • y ∈ V.openSet :=
    fun k y hy => hH₃ k (OpenSubgroup.mem_inf.1 k.2).2 y hy
  have hK₁ : ∀ k ∈ (K : Subgroup G), (ActionOpens.inclusionHom hV₁').label * k *
      (ActionOpens.inclusionHom hV₁').label⁻¹ ∈ (H₁ : Subgroup G) := by
    intro k hk
    simpa [ActionOpens.inclusionHom] using
      (OpenSubgroup.mem_inf.1 (OpenSubgroup.mem_inf.1 hk).1).1
  have hK₂ : ∀ k ∈ (K : Subgroup G), (ActionOpens.inclusionHom hV₂').label * k *
      (ActionOpens.inclusionHom hV₂').label⁻¹ ∈ (H₂ : Subgroup G) := by
    intro k hk
    simpa [ActionOpens.inclusionHom] using
      (OpenSubgroup.mem_inf.1 (OpenSubgroup.mem_inf.1 hk).1).2
  refine ⟨V, hV₁'.trans hV₁U, hV₂'.trans hV₂U, K, hV, hxV₃, fun k => ?_, fun k => ?_⟩
  · have e := map_invariantArrow_map_eq R F₁ (ActionOpens.inclusionHom hV₁') H₁ K hV₁ hV
      hK₁ _ hfix₁ k
    rwa [map_inclusionHom_map_inclusionHom R F₁ hV₁' hV₁U] at e
  · have e := map_invariantArrow_map_eq R F₂ (ActionOpens.inclusionHom hV₂') H₂ K hV₂ hV
      hK₂ _ hfix₂ k
    rwa [map_inclusionHom_map_inclusionHom R F₂ hV₂' hV₂U] at e

omit [IsTopologicalGroup G] [ContinuousConstSMul G X] in
/-- Sums of locally fixed sections are locally fixed. -/
theorem IsLocallyFixedAt.add {F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R}
    {U : ActionOpens G X} {s t : F.obj (op U)} {x : X}
    (hs : IsLocallyFixedAt R F s x) (ht : IsLocallyFixedAt R F t x) :
    IsLocallyFixedAt R F (s + t) x := by
  obtain ⟨V, hV₁, _, K, hV, hxV, h₁, h₂⟩ := IsLocallyFixedAt.exists_common R hs ht
  refine ⟨V, hV₁, K, hV, hxV, fun k => ?_⟩
  simp only [map_add]
  exact congrArg₂ (· + ·) (h₁ k) (h₂ k)

/-- The sections over `U` that are locally fixed at every point of `U`. -/
def smoothSubmodule (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R) (U : ActionOpens G X) :
    Submodule R (F.obj (op U)) where
  carrier := {s | ∀ x ∈ U.openSet, IsLocallyFixedAt R F s x}
  add_mem' hs ht x hx := IsLocallyFixedAt.add R (hs x hx) (ht x hx)
  zero_mem' _ hx := isLocallyFixedAt_zero R F hx
  smul_mem' r _ hs x hx := IsLocallyFixedAt.smul R (hs x hx) r

omit [IsTopologicalGroup G] [ContinuousConstSMul G X] in
/-- A section is smooth exactly when it is locally fixed at every point of its open. -/
theorem mem_smoothSubmodule_iff {F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R}
    {U : ActionOpens G X} (s : F.obj (op U)) :
    s ∈ smoothSubmodule R F U ↔ ∀ x ∈ U.openSet, IsLocallyFixedAt R F s x :=
  Iff.rfl

/-- Restriction and group transport preserve smooth sections. -/
theorem map_mem_smoothSubmodule (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R)
    {U V : ActionOpens G X} (f : V ⟶ U) {s : F.obj (op U)}
    (hs : s ∈ smoothSubmodule R F U) : (F.map f.op).hom s ∈ smoothSubmodule R F V :=
  fun x hx => IsLocallyFixedAt.map_arrow R f hx ((mem_smoothSubmodule_iff R s).1 hs _
    (f.mapsTo x hx))

/-- The transport presheaf of smooth sections. -/
def smoothPresheaf (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R) :
    (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R where
  obj U := ModuleCat.of R (smoothSubmodule R F U.unop)
  map {U V} f := ModuleCat.ofHom ((F.map f).hom.restrict fun _ hs =>
    map_mem_smoothSubmodule R F f.unop hs)
  map_id U := by
    ext s
    simp
  map_comp f g := by
    ext s
    simp

/-- The inclusion of the smooth sections. -/
def smoothPresheafι (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R) : smoothPresheaf R F ⟶ F where
  app U := ModuleCat.ofHom (smoothSubmodule R F U.unop).subtype
  naturality _ _ _ := rfl

/-- Morphisms of transport presheaves send smooth sections to smooth sections. -/
def smoothPresheafMap {F F' : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R} (φ : F ⟶ F') :
    smoothPresheaf R F ⟶ smoothPresheaf R F' where
  app U := ModuleCat.ofHom ((φ.app U).hom.restrict fun s hs x hx =>
    IsLocallyFixedAt.map R φ ((mem_smoothSubmodule_iff R s).1 hs x hx))
  naturality U V f := by
    ext s
    apply Subtype.ext
    exact congrArg (fun k => k.hom s.1) (φ.naturality f)

/-- Smooth sections, functorially in the transport presheaf. -/
@[simps]
def smoothPresheafFunctor :
    ((ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ((ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R) where
  obj := smoothPresheaf R
  map := smoothPresheafMap R
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The smooth sections of an equivariant sheaf satisfy the ordinary sheaf
condition: the gluing in the ambient sheaf of smooth sections is locally fixed
at every point, since it restricts to a smooth section near that point. -/
theorem smoothPresheaf_isSheaf {F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R}
    (hF : sheafProperty G X (ModuleCat.{u} R) F) :
    sheafProperty G X (ModuleCat.{u} R) (smoothPresheaf R F) := by
  have hF' := (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).1 hF
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).2 ?_
  intro ι U sf hsf
  let sf' : ∀ i, F.obj (op ⟨U i⟩) := fun i => (sf i : smoothSubmodule R F ⟨U i⟩).1
  obtain ⟨s, hs, huniq⟩ := hF' U sf' (fun i j => congrArg Subtype.val (hsf i j))
  have hsmooth : s ∈ smoothSubmodule R F ⟨iSup U⟩ := by
    intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
    have hfix := (mem_smoothSubmodule_iff R _).1 (sf i : smoothSubmodule R F ⟨U i⟩).2 x hi
    have hsi : (F.map (ActionOpens.inclusionHom (U := (⟨U i⟩ : ActionOpens G X))
        (V := ⟨iSup U⟩) (Opens.leSupr U i).le).op).hom s = sf' i := hs i
    change IsLocallyFixedAt R F (sf' i) x at hfix
    rw [← hsi] at hfix
    exact IsLocallyFixedAt.of_restrict R _ hfix
  refine ⟨(⟨s, hsmooth⟩ : smoothSubmodule R F ⟨iSup U⟩), fun i => Subtype.ext (hs i),
    fun t ht => Subtype.ext (huniq (t : smoothSubmodule R F ⟨iSup U⟩).1
      fun i => congrArg Subtype.val (ht i))⟩

/-- The equivariant subsheaf of smooth sections. -/
def smoothSubsheafFunctor :
    TopologicalSheaf G X (ModuleCat.{u} R) ⥤ TopologicalSheaf G X (ModuleCat.{u} R) :=
  (sheafProperty G X (ModuleCat.{u} R)).lift
    (toTransportPresheaf G X (ModuleCat.{u} R) ⋙ smoothPresheafFunctor R)
    fun F => smoothPresheaf_isSheaf R F.property

/-- The inclusion of the smooth subsheaf. -/
def smoothSubsheafι : smoothSubsheafFunctor R ⟶ 𝟭 (TopologicalSheaf G X (ModuleCat.{u} R)) where
  app F := ObjectProperty.homMk (smoothPresheafι R F.obj)
  naturality _ _ _ := rfl

instance mono_smoothSubsheafι_app (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    Mono ((smoothSubsheafι R).app F) := by
  have : ∀ U, Mono ((smoothPresheafι R F.obj).app U) := fun U =>
    (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
  have : Mono ((toTransportPresheaf G X (ModuleCat.{u} R)).map ((smoothSubsheafι R).app F)) :=
    NatTrans.mono_of_mono_app (smoothPresheafι R F.obj)
  exact (toTransportPresheaf G X (ModuleCat.{u} R)).mono_of_mono_map this

/-- The smooth subsheaf is smooth. -/
theorem isSmoothSheaf_smoothSubsheaf (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    IsSmoothSheaf R G X ((smoothSubsheafFunctor R).obj F) := by
  intro U s x hx
  obtain ⟨V, hVU, H, hV, hxV, hfix⟩ :=
    (mem_smoothSubmodule_iff R _).1 (s : smoothSubmodule R F.obj U).2 x hx
  exact ⟨V, hVU, H, hV, hxV, fun h => Subtype.ext (hfix h)⟩

/-- The smooth part of an equivariant module sheaf, as a smooth sheaf. -/
def smoothCoreflector : TopologicalSheaf G X (ModuleCat.{u} R) ⥤ SmoothTopologicalSheaf R G X :=
  (smoothSheafProperty R G X).lift (smoothSubsheafFunctor R) (isSmoothSheaf_smoothSubsheaf R)

/-- A morphism from a smooth sheaf factors through the smooth subsheaf. -/
def smoothLift {S F : TopologicalSheaf G X (ModuleCat.{u} R)} (hS : IsSmoothSheaf R G X S)
    (f : S ⟶ F) : S ⟶ (smoothSubsheafFunctor R).obj F :=
  ObjectProperty.homMk
    { app U := ModuleCat.ofHom (LinearMap.codRestrict _ (f.hom.app U).hom fun s x hx =>
        IsLocallyFixedAt.map R f.hom (hS U.unop s x hx))
      naturality U V g := by
        ext s
        apply Subtype.ext
        exact congrArg (fun k => k.hom s) (f.hom.naturality g) }

@[reassoc (attr := simp)]
theorem smoothLift_comp_ι {S F : TopologicalSheaf G X (ModuleCat.{u} R)}
    (hS : IsSmoothSheaf R G X S) (f : S ⟶ F) :
    smoothLift R hS f ≫ (smoothSubsheafι R).app F = f :=
  rfl

/-- The smooth part is right adjoint to the inclusion of smooth sheaves. -/
def smoothAdjunction : smoothInclusion R G X ⊣ smoothCoreflector R :=
  Adjunction.mkOfHomEquiv
    { homEquiv S F :=
        { toFun f := ObjectProperty.homMk (smoothLift R S.property f)
          invFun g := g.hom ≫ (smoothSubsheafι R).app F
          left_inv _ := rfl
          right_inv _ := rfl }
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := rfl }

omit [IsTopologicalGroup G] [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] in
instance smoothInclusion_full : (smoothInclusion R G X).Full :=
  inferInstanceAs (smoothSheafProperty R G X).ι.Full

omit [IsTopologicalGroup G] [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] in
instance smoothInclusion_faithful : (smoothInclusion R G X).Faithful :=
  inferInstanceAs (smoothSheafProperty R G X).ι.Faithful

instance smoothInclusion_coreflective : Coreflective (smoothInclusion R G X) where
  R := smoothCoreflector R
  adj := smoothAdjunction R

end Fixing

end Langlands.Sheaf.Equivariant
