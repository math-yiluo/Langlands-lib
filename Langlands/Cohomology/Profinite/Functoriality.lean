import Langlands.Cohomology.Profinite.Cochains

/-!
# Functoriality of the cohomology of topological groups

A continuous homomorphism `φ : H →ₜ* G` and a morphism `f : Rep.res φ A ⟶ B` of
`H`-representations induce the cochain map `c ↦ f ∘ c ∘ φⁿ` (`cochainsMap φ f`) and the map
`map φ f n : cohomology A n ⟶ cohomology B n`. This one definition covers coefficient maps
(`φ = .id G`), restriction to a subgroup (`res`, with `φ` the inclusion `subgroupInclusion S`
and `f = 𝟙`) and inflation from a quotient (`infl`, with `φ` the projection `quotientMap N` and
`f` the inclusion of the `N`-invariants). It follows the shape of Mathlib's
`ContinuousCohomology.map`.

`cohomologyFunctor k G n` is cohomology as a functor on the Library's category `SmoothRep k G`.
-/

open CategoryTheory groupCohomology

namespace Langlands.ProfiniteCohomology

universe u

variable {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]
  [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace K]

/-- The inclusion of a subgroup, as a continuous homomorphism. -/
abbrev subgroupInclusion (S : Subgroup G) : S →ₜ* G :=
  ⟨S.subtype, continuous_subtype_val⟩

/-- The projection onto a quotient group, as a continuous homomorphism. -/
abbrev quotientMap (N : Subgroup G) [N.Normal] : G →ₜ* G ⧸ N :=
  ⟨QuotientGroup.mk' N, QuotientGroup.continuous_mk⟩

theorem continuous_subgroup_subtype (S : Subgroup G) : Continuous S.subtype :=
  continuous_subtype_val

theorem continuous_quotientGroup_mk' (N : Subgroup G) [N.Normal] :
    Continuous (QuotientGroup.mk' N) :=
  QuotientGroup.continuous_mk

variable [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalGroup K]

section Cochains

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
theorem isLocallyConstant_cochainsMap {A : Rep.{u} k G} {B : Rep.{u} k H} (φ : H →ₜ* G)
    (f : Rep.res (φ : H →* G) A ⟶ B) {n : ℕ} {x : (Fin n → G) → A}
    (hx : IsLocallyConstant x) :
    IsLocallyConstant (((groupCohomology.cochainsMap (φ : H →* G) f).f n).hom x) := by
  have hc : Continuous fun h : Fin n → H => (⇑φ ∘ h) :=
    continuous_pi fun i => φ.continuous_toFun.comp (continuous_apply i)
  exact (hx.comp_continuous hc).comp _

/-- The map of locally constant cochains `c ↦ f ∘ c ∘ φⁿ` induced by a continuous homomorphism
`φ : H →ₜ* G` and a morphism `f : Rep.res φ A ⟶ B`. -/
noncomputable def cochainsMap {A : Rep.{u} k G} {B : Rep.{u} k H} [IsSmoothRep A]
    [IsSmoothRep B] (φ : H →ₜ* G) (f : Rep.res (φ : H →* G) A ⟶ B) :
    cochains A ⟶ cochains B where
  f n := ModuleCat.ofHom (((groupCohomology.cochainsMap (φ : H →* G) f).f n).hom.restrict
    fun _ hx => isLocallyConstant_cochainsMap φ f hx)
  comm' i j (hij : i + 1 = j) := by
    subst hij
    rw [cochains_d, cochains_d]
    ext x : 2
    apply Subtype.ext
    have h := (groupCohomology.cochainsMap (φ : H →* G) f).comm i (i + 1)
    rw [groupCohomology.inhomogeneousCochains.d_def,
      groupCohomology.inhomogeneousCochains.d_def] at h
    exact congrArg (fun ψ => ψ.hom x.1) h

variable {A : Rep.{u} k G} {B : Rep.{u} k H} [IsSmoothRep A] [IsSmoothRep B]
  (φ : H →ₜ* G) (f : Rep.res (φ : H →* G) A ⟶ B)

theorem cochainsι_cochainsMap_apply (n : ℕ) (x : (cochains A).X n) :
    ((cochainsι B).f n).hom (((cochainsMap φ f).f n).hom x) =
      fun h => f.hom (((cochainsι A).f n).hom x (⇑φ ∘ h)) :=
  rfl

@[reassoc]
theorem cochainsMap_comp_cochainsι :
    cochainsMap φ f ≫ cochainsι B = cochainsι A ≫ groupCohomology.cochainsMap (φ : H →* G) f := by
  ext n x : 3
  rfl

@[simp]
theorem cochainsMap_id : cochainsMap (.id G) (𝟙 A) = 𝟙 _ := by
  ext n x : 3
  rfl

@[reassoc]
theorem cochainsMap_comp {C : Rep.{u} k K} [IsSmoothRep C] (ψ : K →ₜ* H)
    (g : Rep.res (ψ : K →* H) B ⟶ C) :
    cochainsMap (φ.comp ψ) ((Rep.resFunctor (ψ : K →* H)).map f ≫ g) =
      cochainsMap φ f ≫ cochainsMap ψ g := by
  ext n x : 3
  rfl

@[reassoc]
theorem cochainsMap_id_comp {A B C : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B]
    [IsSmoothRep C] (f : A ⟶ B) (g : B ⟶ C) :
    cochainsMap (.id G) (f ≫ g : A ⟶ C) = cochainsMap (.id G) f ≫ cochainsMap (.id G) g := by
  ext n x : 3
  rfl

@[simp]
theorem cochainsMap_zero : cochainsMap φ (0 : Rep.res (φ : H →* G) A ⟶ B) = 0 := by
  ext n x : 3
  rfl

@[simp]
theorem cochainsMap_id_zero {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] :
    cochainsMap (.id G) (0 : A ⟶ B) = 0 := by
  ext n x : 3
  rfl

instance {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] (f : A ⟶ B) [Mono f] (n : ℕ) :
    Mono ((cochainsMap (.id G) f).f n) := by
  rw [ModuleCat.mono_iff_injective]
  intro c d h
  apply Subtype.ext
  funext x
  exact (Rep.mono_iff_injective f).1 ‹_› (congrFun (congrArg Subtype.val h) x)

instance {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] (f : A ⟶ B) [Epi f] (n : ℕ) :
    Epi ((cochainsMap (.id G) f).f n) := by
  rw [ModuleCat.epi_iff_surjective]
  intro d
  obtain ⟨s, hs⟩ := ((Rep.epi_iff_surjective f).1 ‹_›).hasRightInverse
  let d' : locallyConstantCochains B n := d
  refine ⟨(⟨s ∘ d'.1, (mem_locallyConstantCochains A _).2 (IsLocallyConstant.comp d'.2 s)⟩ :
    locallyConstantCochains A n), Subtype.ext ?_⟩
  funext x
  exact hs _

end Cochains

section Cohomology

variable {A : Rep.{u} k G} {B : Rep.{u} k H} [IsSmoothRep A] [IsSmoothRep B]
  (φ : H →ₜ* G) (f : Rep.res (φ : H →* G) A ⟶ B)

/-- The map on cocycles induced by `φ : H →ₜ* G` and `f : Rep.res φ A ⟶ B`. -/
noncomputable abbrev cocyclesMap (n : ℕ) : cocycles A n ⟶ cocycles B n :=
  HomologicalComplex.cyclesMap (cochainsMap φ f) n

/-- The map `Hⁿ(G, A) ⟶ Hⁿ(H, B)` induced by a continuous homomorphism `φ : H →ₜ* G` and a
morphism `f : Rep.res φ A ⟶ B` of `H`-representations. For `φ = .id G` it is the map induced by
a morphism of coefficients. -/
noncomputable def map (n : ℕ) : cohomology A n ⟶ cohomology B n :=
  HomologicalComplex.homologyMap (cochainsMap φ f) n

@[reassoc, elementwise]
theorem cohomologyπ_map (n : ℕ) :
    cohomologyπ A n ≫ map φ f n = cocyclesMap φ f n ≫ cohomologyπ B n := by
  simp [map, cocyclesMap, cohomologyπ, cohomology]

@[simp]
theorem map_id (n : ℕ) : map (.id G) (𝟙 A) n = 𝟙 _ := by
  unfold map
  rw [cochainsMap_id]
  exact HomologicalComplex.homologyMap_id _ _

@[reassoc]
theorem map_comp {C : Rep.{u} k K} [IsSmoothRep C] (ψ : K →ₜ* H)
    (g : Rep.res (ψ : K →* H) B ⟶ C) (n : ℕ) :
    map (φ.comp ψ) ((Rep.resFunctor (ψ : K →* H)).map f ≫ g) n = map φ f n ≫ map ψ g n := by
  rw [map, cochainsMap_comp, HomologicalComplex.homologyMap_comp]
  rfl

@[reassoc]
theorem map_id_comp {A B C : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B]
    [IsSmoothRep C] (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    map (.id G) (f ≫ g : A ⟶ C) n = map (.id G) f n ≫ map (.id G) g n := by
  unfold map
  rw [cochainsMap_id_comp, HomologicalComplex.homologyMap_comp]
  rfl

@[simp]
theorem map_zero_eq_zero (n : ℕ) : map φ (0 : Rep.res (φ : H →* G) A ⟶ B) n = 0 := by
  rw [map, cochainsMap_zero]
  exact HomologicalComplex.homologyMap_zero _ _ _

@[simp]
theorem map_id_zero {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] (n : ℕ) :
    map (.id G) (0 : A ⟶ B) n = 0 := by
  unfold map
  rw [cochainsMap_id_zero]
  exact HomologicalComplex.homologyMap_zero _ _ _

end Cohomology

section Coefficients

variable {A B C : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] [IsSmoothRep C]

/-- The map of cochain complexes induced by a morphism of coefficients `f : A ⟶ B`: it is
`cochainsMap (.id G) f`, as an abbreviation that reads `A` and `B` off `f`. -/
noncomputable abbrev coeffCochainsMap (f : A ⟶ B) : cochains A ⟶ cochains B :=
  cochainsMap (.id G) f

/-- The map on cohomology induced by a morphism of coefficients `f : A ⟶ B`: it is
`map (.id G) f n`, as an abbreviation that reads `A` and `B` off `f` (elaborating
`map (.id G) f n` has to recover `A` from `Rep.res (.id G) A`, which fails when `A` is not a
variable). -/
noncomputable abbrev coeffMap (f : A ⟶ B) (n : ℕ) : cohomology A n ⟶ cohomology B n :=
  map (.id G) f n

theorem coeffMap_eq (f : A ⟶ B) (n : ℕ) : coeffMap f n = map (.id G) f n :=
  rfl

theorem coeffCochainsMap_eq (f : A ⟶ B) : coeffCochainsMap f = cochainsMap (.id G) f :=
  rfl

theorem coeffMap_def (f : A ⟶ B) (n : ℕ) :
    coeffMap f n = HomologicalComplex.homologyMap (coeffCochainsMap f) n :=
  rfl

@[simp]
theorem coeffCochainsMap_id : coeffCochainsMap (𝟙 A) = 𝟙 (cochains A) :=
  cochainsMap_id

@[reassoc]
theorem coeffCochainsMap_comp (f : A ⟶ B) (g : B ⟶ C) :
    coeffCochainsMap (f ≫ g) = coeffCochainsMap f ≫ coeffCochainsMap g :=
  cochainsMap_id_comp f g

@[simp]
theorem coeffCochainsMap_zero : coeffCochainsMap (0 : A ⟶ B) = 0 :=
  cochainsMap_id_zero

@[simp]
theorem coeffMap_id (n : ℕ) : coeffMap (𝟙 A) n = 𝟙 _ :=
  map_id n

@[reassoc]
theorem coeffMap_comp (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    coeffMap (f ≫ g) n = coeffMap f n ≫ coeffMap g n :=
  map_id_comp f g n

@[simp]
theorem coeffMap_zero (n : ℕ) : coeffMap (0 : A ⟶ B) n = 0 :=
  map_id_zero n

@[reassoc, elementwise]
theorem cohomologyπ_coeffMap (f : A ⟶ B) (n : ℕ) :
    cohomologyπ A n ≫ coeffMap f n =
      HomologicalComplex.cyclesMap (coeffCochainsMap f) n ≫ cohomologyπ B n :=
  cohomologyπ_map (.id G) f n

instance (f : A ⟶ B) [Mono f] (n : ℕ) : Mono ((coeffCochainsMap f).f n) :=
  inferInstanceAs (Mono ((cochainsMap (.id G) f).f n))

instance (f : A ⟶ B) [Epi f] (n : ℕ) : Epi ((coeffCochainsMap f).f n) :=
  inferInstanceAs (Epi ((cochainsMap (.id G) f).f n))

end Coefficients

section Functor

variable (k G)

/-- The complex of locally constant cochains, as a functor on smooth representations. -/
@[simps]
noncomputable def cochainsFunctor : SmoothRep.{u, u, u} k G ⥤ CochainComplex (ModuleCat k) ℕ where
  obj A := cochains A.obj
  map f := cochainsMap (.id G) f.hom
  map_id _ := cochainsMap_id
  map_comp f g := cochainsMap_id_comp f.hom g.hom

/-- Cohomology in degree `n`, as a functor on smooth representations. -/
noncomputable def cohomologyFunctor (n : ℕ) : SmoothRep.{u, u, u} k G ⥤ ModuleCat k :=
  cochainsFunctor k G ⋙ HomologicalComplex.homologyFunctor _ _ n

theorem cohomologyFunctor_obj (n : ℕ) (A : SmoothRep.{u, u, u} k G) :
    (cohomologyFunctor k G n).obj A = cohomology A.obj n :=
  rfl

theorem cohomologyFunctor_map (n : ℕ) {A B : SmoothRep.{u, u, u} k G} (f : A ⟶ B) :
    (cohomologyFunctor k G n).map f = map (.id G) f.hom n :=
  rfl

instance : (cochainsFunctor k G).Additive where
  map_add {_ _ f g} := by
    ext n c : 3
    apply Subtype.ext
    funext x
    rfl

instance (n : ℕ) : (cohomologyFunctor k G n).Additive := by
  unfold cohomologyFunctor
  infer_instance

end Functor

section Restriction

variable (A : Rep.{u} k G) [IsSmoothRep A]

/-- Restriction `Hⁿ(G, A) ⟶ Hⁿ(S, A)` to a subgroup `S`. -/
noncomputable abbrev res (S : Subgroup G) (n : ℕ) :
    cohomology A n ⟶ cohomology (Rep.res S.subtype A) n :=
  map (subgroupInclusion S) (𝟙 (Rep.res S.subtype A)) n

theorem res_eq (S : Subgroup G) (n : ℕ) :
    res A S n = map (subgroupInclusion S) (𝟙 (Rep.res S.subtype A)) n :=
  rfl

set_option backward.isDefEq.respectTransparency false in
-- The coefficient map `g : A ⟶ A'` is used at type `Rep.res (.id G) A ⟶ A'`, which is a
-- definitional but not a reducible equality.
@[reassoc]
theorem res_naturality {A' : Rep.{u} k G} [IsSmoothRep A'] (g : A ⟶ A')
    (S : Subgroup G) (n : ℕ) :
    map (.id G) g n ≫ res A' S n =
      res A S n ≫ map (.id S) ((Rep.resFunctor S.subtype).map g) n := by
  rw [res, res, ← map_comp, ← map_comp]
  rfl

end Restriction

section Inflation

variable (A : Rep.{u} k G) [IsSmoothRep A]

/-- Inflation `Hⁿ(G/N, A^N) ⟶ Hⁿ(G, A)` from the quotient by a normal subgroup `N`. -/
noncomputable abbrev infl (N : Subgroup G) [N.Normal] (n : ℕ) :
    cohomology (A.quotientToInvariants N) n ⟶ cohomology A n :=
  map (quotientMap N) (Rep.ofHom (A.ρ.quotientToInvariants_lift N)) n

theorem infl_eq (N : Subgroup G) [N.Normal] (n : ℕ) :
    infl A N n = map (quotientMap N) (Rep.ofHom (A.ρ.quotientToInvariants_lift N)) n :=
  rfl

instance isSmoothRep_quotientToInvariantsFunctor_obj (N : Subgroup G) [N.Normal] :
    IsSmoothRep ((Rep.quotientToInvariantsFunctor k N).obj A) :=
  isSmoothRep_quotientToInvariants A N

end Inflation

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

open CategoryTheory

universe u

section Iso

/-- The map of an isomorphism of modules on cohomology is bijective. -/
theorem bijective_coeffMap_of_iso {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {A B : Rep.{u} (ULift.{u} ℤ) G} [IsSmoothRep A] [IsSmoothRep B]
    (e : A ≅ B) (r : ℕ) : Function.Bijective (coeffMap e.hom r).hom := by
  refine Function.bijective_iff_has_inverse.2 ⟨(coeffMap e.inv r).hom, fun x => ?_, fun y => ?_⟩
  · rw [← ModuleCat.comp_apply, ← coeffMap_comp, e.hom_inv_id, coeffMap_id]
    rfl
  · rw [← ModuleCat.comp_apply, ← coeffMap_comp, e.inv_hom_id, coeffMap_id]
    rfl

end Iso

end Langlands.ProfiniteCohomology
