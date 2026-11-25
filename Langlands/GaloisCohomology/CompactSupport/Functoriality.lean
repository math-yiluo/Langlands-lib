import Langlands.GaloisCohomology.CompactSupport.Basic

/-!
# Functoriality of cohomology with compact support and the connecting map

A map `g : A ⟶ B` of `G`-modules with maps `g_v : A_v ⟶ B_v` compatible with `a` and `b`
induces maps of cochains with compact support and of `H_c^n` (`compactSupportMap`), functorial
in `(g, g_v)` and compatible with `globalToLocal` and `localToCompact`. A short exact sequence of
`G`-modules `0 → A₁ → A₂ → A₃ → 0` with compatible short exact sequences of `H_v`-modules gives a
short exact sequence of cochains with compact support, hence the connecting map
`compactSupportδ : H_c^n(G, A₃) ⟶ H_c^{n+1}(G, A₁)` and the long exact sequence
`⋯ ⟶ H_c^n(A₁) ⟶ H_c^n(A₂) ⟶ H_c^n(A₃) ⟶ H_c^{n+1}(A₁) ⟶ ⋯`.
-/

namespace Langlands.GaloisCohomology

open Langlands Langlands.ProfiniteCohomology CategoryTheory Limits

universe u

section CompactSupport

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)

section Functoriality

variable {A B C : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] [IsSmoothRep C]
  {Aᵥ Bᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsSmoothRep (Aᵥ v)] [∀ v, IsSmoothRep (Bᵥ v)]
  [∀ v, IsSmoothRep (Cᵥ v)] {a : ∀ v, Rep.res (φ v : H v →* G) A ⟶ Aᵥ v}
  {b : ∀ v, Rep.res (φ v : H v →* G) B ⟶ Bᵥ v} {c : ∀ v, Rep.res (φ v : H v →* G) C ⟶ Cᵥ v}

omit [IsSmoothRep C] in
/-- Restriction along `ψ` commutes with maps of coefficients compatible with the local maps. -/
theorem cochainsMap_comp_coeffCochainsMap {H' : Type u} [Group H'] [TopologicalSpace H']
    [IsTopologicalGroup H'] (ψ : H' →ₜ* G)
    {A' B' : Rep.{u} k H'} [IsSmoothRep A'] [IsSmoothRep B'] (a' : Rep.res (ψ : H' →* G) A ⟶ A')
    (b' : Rep.res (ψ : H' →* G) B ⟶ B') (g : A ⟶ B) (g' : A' ⟶ B')
    (hg : a' ≫ g' = (Rep.resFunctor (ψ : H' →* G)).map g ≫ b') :
    cochainsMap ψ a' ≫ coeffCochainsMap g' = coeffCochainsMap g ≫ cochainsMap ψ b' := by
  ext n x : 3
  apply Subtype.ext
  funext σ
  exact congrArg (fun F : Rep.res (ψ : H' →* G) A ⟶ B' => F.hom (x.1 (⇑ψ ∘ σ))) hg

/-- `localRes` is natural in compatible maps of the global and local coefficients. -/
theorem localRes_naturality (g : A ⟶ B) (gᵥ : ∀ v, Aᵥ v ⟶ Bᵥ v)
    (hg : ∀ v, a v ≫ gᵥ v = (Rep.resFunctor (φ v : H v →* G)).map g ≫ b v) :
    localRes φ A Aᵥ a ≫ piMap (fun v => coeffCochainsMap (gᵥ v)) =
      coeffCochainsMap g ≫ localRes φ B Bᵥ b := by
  rw [localRes, localRes, piLift_piMap]
  refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext (LinearMap.ext fun x =>
    funext fun v => ?_)
  exact hom_apply_hom_apply_eq_of_comp_eq (congrArg (·.f n)
    (cochainsMap_comp_coeffCochainsMap (φ v) (a v) (b v) g (gᵥ v)
      (hg v))) x

/-- The map of cochains with compact support induced by `g : A ⟶ B` and compatible local maps `g_v
: A_v ⟶ B_v`. -/
noncomputable def compactSupportCochainsMap (g : A ⟶ B) (gᵥ : ∀ v, Aᵥ v ⟶ Bᵥ v)
    (hg : ∀ v, a v ≫ gᵥ v = (Rep.resFunctor (φ v : H v →* G)).map g ≫ b v) :
    compactSupportCochains φ A Aᵥ a ⟶ compactSupportCochains φ B Bᵥ b :=
  mappingCoconeNat.map (coeffCochainsMap g) (piMap fun v => coeffCochainsMap (gᵥ v))
    (localRes_naturality φ g gᵥ hg)

/-- The map `H_c^n(G, A) ⟶ H_c^n(G, B)` induced by `g : A ⟶ B` and compatible local maps `g_v :
A_v ⟶ B_v`. -/
noncomputable def compactSupportMap (g : A ⟶ B) (gᵥ : ∀ v, Aᵥ v ⟶ Bᵥ v)
    (hg : ∀ v, a v ≫ gᵥ v = (Rep.resFunctor (φ v : H v →* G)).map g ≫ b v) (n : ℕ) :
    compactSupportCohomology φ A Aᵥ a n ⟶ compactSupportCohomology φ B Bᵥ b n :=
  HomologicalComplex.homologyMap (compactSupportCochainsMap φ g gᵥ hg) n

omit [∀ v, IsSmoothRep (Bᵥ v)] [∀ v, IsSmoothRep (Cᵥ v)] [IsSmoothRep B] [IsSmoothRep C] in
@[simp]
theorem compactSupportMap_id (n : ℕ) :
    compactSupportMap φ (𝟙 A) (fun v => 𝟙 (Aᵥ v)) (a := a) (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm) n = 𝟙 _ := by
  have h : compactSupportCochainsMap φ (𝟙 A) (fun v => 𝟙 (Aᵥ v)) (a := a) (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm) = 𝟙 _ := by
    ext n : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun (p : (cochains A).X n ×
      shiftNegOneX (piComplex fun v => cochains (Aᵥ v)) n) => Prod.ext rfl ?_)
    cases n with
    | zero => rfl
    | succ n => rfl
  exact (congrArg (HomologicalComplex.homologyMap · n) h).trans
    (HomologicalComplex.homologyMap_id _ n)

variable (g : A ⟶ B) (gᵥ : ∀ v, Aᵥ v ⟶ Bᵥ v)
  (hg : ∀ v, a v ≫ gᵥ v = (Rep.resFunctor (φ v : H v →* G)).map g ≫ b v)

theorem compactSupportMap_comp (g' : B ⟶ C) (gᵥ' : ∀ v, Bᵥ v ⟶ Cᵥ v)
    (hg' : ∀ v, b v ≫ gᵥ' v = (Rep.resFunctor (φ v : H v →* G)).map g' ≫ c v) (n : ℕ) :
    compactSupportMap φ (g ≫ g') (fun v => gᵥ v ≫ gᵥ' v)
        (fun v => by rw [reassoc_of% hg v, hg' v, Functor.map_comp, Category.assoc]) n =
      compactSupportMap φ g gᵥ hg n ≫ compactSupportMap φ g' gᵥ' hg' n := by
  have h : compactSupportCochainsMap φ (g ≫ g') (fun v => gᵥ v ≫ gᵥ' v)
      (fun v => by rw [reassoc_of% hg v, hg' v, Functor.map_comp, Category.assoc]) =
      compactSupportCochainsMap φ g gᵥ hg ≫ compactSupportCochainsMap φ g' gᵥ' hg' := by
    ext n : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun (p : (cochains A).X n ×
      shiftNegOneX (piComplex fun v => cochains (Aᵥ v)) n) => Prod.ext rfl ?_)
    cases n with
    | zero => rfl
    | succ n => rfl
  exact (congrArg (HomologicalComplex.homologyMap · n) h).trans
    (HomologicalComplex.homologyMap_comp _ _ n)

include hg in

theorem cohomologyMap_globalToLocal (n : ℕ) :
    coeffMap g n ≫ globalToLocal φ B Bᵥ b n =
      globalToLocal φ A Aᵥ a n ≫ ModuleCat.ofHom (LinearMap.pi fun v =>
        (coeffMap (gᵥ v) n).hom.comp (LinearMap.proj v)) := by
  have h := congrArg (fun F => HomologicalComplex.homologyMap F n ≫ (localCohomologyIso Bᵥ n).hom)
    (localRes_naturality φ g gᵥ hg)
  simp only [HomologicalComplex.homologyMap_comp, Category.assoc] at h
  have e1 : HomologicalComplex.homologyMap (localRes φ A Aᵥ a) n ≫
      HomologicalComplex.homologyMap (piMap fun v => coeffCochainsMap (gᵥ v)) n ≫
        (localCohomologyIso Bᵥ n).hom =
      (HomologicalComplex.homologyMap (localRes φ A Aᵥ a) n ≫ (localCohomologyIso Aᵥ n).hom) ≫
        ModuleCat.ofHom (LinearMap.pi fun v =>
          (coeffMap (gᵥ v) n).hom.comp (LinearMap.proj v)) := by
    exact (congrArg (HomologicalComplex.homologyMap (localRes φ A Aᵥ a) n ≫ ·)
      (homologyMap_piMap_piHomologyIso_hom (fun v => coeffCochainsMap (gᵥ v)) n)).trans
      (Category.assoc _ _ _).symm
  exact (congrArg (coeffMap g n ≫ ·)
    (homologyMap_localRes_localCohomologyIso_hom φ B Bᵥ b n).symm).trans (h.symm.trans (e1.trans
      (congrArg (· ≫ ModuleCat.ofHom (LinearMap.pi fun v =>
          (coeffMap (gᵥ v) n).hom.comp (LinearMap.proj v)))
        (homologyMap_localRes_localCohomologyIso_hom φ A Aᵥ a n))))

theorem localToCompact_compactSupportMap (n : ℕ) :
    localToCompact φ A Aᵥ a n ≫ compactSupportMap φ g gᵥ hg (n + 1) =
      ModuleCat.ofHom (LinearMap.pi fun v => (coeffMap (gᵥ v) n).hom.comp (LinearMap.proj v)) ≫
        localToCompact φ B Bᵥ b n := by
  have h2 : (localCohomologyIso Aᵥ n).inv ≫
      HomologicalComplex.homologyMap (piMap fun v => coeffCochainsMap (gᵥ v)) n =
      ModuleCat.ofHom (LinearMap.pi fun v => (coeffMap (gᵥ v) n).hom.comp (LinearMap.proj v)) ≫
        (localCohomologyIso Bᵥ n).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact homologyMap_piMap_piHomologyIso_hom _ n
  have h := congrArg ((localCohomologyIso Aᵥ n).inv ≫ ·)
    (mappingCoconeNat.homologyδ_naturality (coeffCochainsMap g) (piMap fun v => coeffCochainsMap (gᵥ v))
      (localRes_naturality φ g gᵥ hg) n)
  simp only [← Category.assoc] at h
  rw [h2, Category.assoc] at h
  exact h

end Functoriality

section CoefficientSequence

variable (S : ShortComplex (Rep.{u} k G)) [IsSmoothRep S.X₁] [IsSmoothRep S.X₂]
  [IsSmoothRep S.X₃] (Sᵥ : ∀ v, ShortComplex (Rep.{u} k (H v))) [∀ v, IsSmoothRep (Sᵥ v).X₁]
  [∀ v, IsSmoothRep (Sᵥ v).X₂] [∀ v, IsSmoothRep (Sᵥ v).X₃]
  (s : ∀ v, S.map (Rep.resFunctor (φ v : H v →* G)) ⟶ Sᵥ v)

/-- `localRes` for the three terms of a short complex of coefficients, as a morphism of short
complexes of complexes. -/
noncomputable def localResShortComplex :
    cochainsShortComplex S ⟶ piShortComplex fun v => cochainsShortComplex (Sᵥ v) where
  τ₁ := localRes φ S.X₁ (fun v => (Sᵥ v).X₁) fun v => (s v).τ₁
  τ₂ := localRes φ S.X₂ (fun v => (Sᵥ v).X₂) fun v => (s v).τ₂
  τ₃ := localRes φ S.X₃ (fun v => (Sᵥ v).X₃) fun v => (s v).τ₃
  comm₁₂ := localRes_naturality φ S.f (fun v => (Sᵥ v).f) fun v => (s v).comm₁₂
  comm₂₃ := localRes_naturality φ S.g (fun v => (Sᵥ v).g) fun v => (s v).comm₂₃

theorem compactSupportMap_f_g (n : ℕ) :
    compactSupportMap φ S.f (fun v => (Sᵥ v).f) (fun v => (s v).comm₁₂) n ≫
      compactSupportMap φ S.g (fun v => (Sᵥ v).g) (fun v => (s v).comm₂₃) n = 0 :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (HomologicalComplex.homologyMap · n)
      (mappingCoconeNat.mapShortComplex (localResShortComplex φ S Sᵥ s)).zero).trans
      (HomologicalComplex.homologyMap_zero _ _ n))

variable {S Sᵥ}

theorem compactSupportCochains_shortExact (hS : S.ShortExact) (hSᵥ : ∀ v, (Sᵥ v).ShortExact) :
    (mappingCoconeNat.mapShortComplex (localResShortComplex φ S Sᵥ s)).ShortExact :=
  mappingCoconeNat.shortExact_mapShortComplex _ (cochainsShortComplex_shortExact hS)
    (piShortComplex_shortExact fun v => cochainsShortComplex_shortExact (hSᵥ v))

variable (hS : S.ShortExact) (hSᵥ : ∀ v, (Sᵥ v).ShortExact)

/-- The connecting map `H_c^n(G, A₃) ⟶ H_c^{n+1}(G, A₁)` of a short exact sequence of global
coefficients with compatible short exact sequences of local coefficients. -/
noncomputable def compactSupportδ (hS : S.ShortExact) (hSᵥ : ∀ v, (Sᵥ v).ShortExact) (n : ℕ) :
    compactSupportCohomology φ S.X₃ (fun v => (Sᵥ v).X₃) (fun v => (s v).τ₃) n ⟶
      compactSupportCohomology φ S.X₁ (fun v => (Sᵥ v).X₁) (fun v => (s v).τ₁) (n + 1) :=
  (compactSupportCochains_shortExact φ s hS hSᵥ).δ n (n + 1) rfl

include hS hSᵥ in

theorem compactSupportCohomology_exact₂ (n : ℕ) :
    (ShortComplex.mk (compactSupportMap φ S.f (fun v => (Sᵥ v).f) (fun v => (s v).comm₁₂) n)
      (compactSupportMap φ S.g (fun v => (Sᵥ v).g) (fun v => (s v).comm₂₃) n)
      (compactSupportMap_f_g φ S Sᵥ s n)).Exact :=
  (compactSupportCochains_shortExact φ s hS hSᵥ).homology_exact₂ n

theorem compactSupportCohomology_exact₃ (n : ℕ) :
    (ShortComplex.mk (compactSupportMap φ S.g (fun v => (Sᵥ v).g) (fun v => (s v).comm₂₃) n)
      (compactSupportδ φ s hS hSᵥ n)
      ((compactSupportCochains_shortExact φ s hS hSᵥ).comp_δ n (n + 1) rfl)).Exact :=
  (compactSupportCochains_shortExact φ s hS hSᵥ).homology_exact₃ n (n + 1) rfl

theorem compactSupportCohomology_exact₁ (n : ℕ) :
    (ShortComplex.mk (compactSupportδ φ s hS hSᵥ n)
      (compactSupportMap φ S.f (fun v => (Sᵥ v).f) (fun v => (s v).comm₁₂) (n + 1))
      ((compactSupportCochains_shortExact φ s hS hSᵥ).δ_comp n (n + 1) rfl)).Exact :=
  (compactSupportCochains_shortExact φ s hS hSᵥ).homology_exact₁ n (n + 1) rfl

end CoefficientSequence


section ResMorphism

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
  (D : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep D] {n : ℕ} (hD : ∀ d : D, n • d = 0)
  (U : OpenSubgroup G)

variable {D} in
/-- A morphism `g : A ⟶ B` as a morphism of the restrictions to `H_v`. -/
def resMorphism {A B : Rep.{u} (ULift.{u} ℤ) G} (g : A ⟶ B) (v : ι) :
    Rep.res (φ v : Hv v →* G) A ⟶ Rep.res (φ v : Hv v →* G) B :=
  Rep.ofHom ⟨g.hom.toLinearMap, fun h => LinearMap.ext fun a => Rep.hom_comm_apply g (φ v h) a⟩

omit [IsTopologicalGroup G] [CompactSpace G] [∀ v, IsTopologicalGroup (Hv v)]
  [∀ v, CompactSpace (Hv v)] [IsSmoothRep D] in
theorem resMorphism_eq {A B : Rep.{u} (ULift.{u} ℤ) G} (g : A ⟶ B) (v : ι) :
    resMorphism φ g v = (Rep.resFunctor (φ v : Hv v →* G)).map g :=
  Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))

end ResMorphism

end CompactSupport

end Langlands.GaloisCohomology
