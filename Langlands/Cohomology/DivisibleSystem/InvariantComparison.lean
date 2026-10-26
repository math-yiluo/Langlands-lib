import Langlands.Cohomology.DivisibleSystem.TotalExact
import Langlands.Cohomology.DivisibleSystem.ProPInvariants
import Langlands.Cohomology.ExtendMap

/-!
# Comparison of Harris's `C_m^{•,H}` with the underlying complexes

Harris 1999, §2, pp.305–306, takes an open normal pro-`p` subgroup `H` of `S(ẽ)` acting
trivially on the compactly supported cohomology `H_c^q(U(ẽ)_F̄, ℤ/ℓ^mℤ)`, which his (2.3)
identifies with the cohomology of the compact-section complex `G_m^•(U(ẽ)_F̄)`. Since
`H⁰(H, ·)` is exact, the inclusion
`G_m^•(U(ẽ)_F̄)^H ↪ G_m^•(U(ẽ)_F̄)` is a quasi-isomorphism, and `C_m^{•,H}` resolves the
`H`-invariants. This module composes the two comparisons, at a fixed `H`.

For an `ℓ`-divisible system `K` of `ℕ`-graded complexes of smooth representations of `G`,
vanishing in degrees `q ≥ N`, and `H` normal of finite index, it builds a morphism of
`ℓ`-divisible systems from the inflation along `G ⟶ G ⧸ H` of `C_m^{•,H}`
(`quotientInvariantsTotalSystem`) to the underlying complexes of representations of `K` extended
to `ℤ`. It is a quasi-isomorphism at every level `m` at which `H` acts trivially on the
cohomology of the complex of representations (not identified here with a geometric
cohomology), given Worker 3's unproved `ProPInvariantSubcomplexStatement` (a hypothesis `hS`), for
`H` pro-`p` and `p` invertible in the coefficients. The surjectivity on `H`-invariants is the
explicit hypothesis `hK`, or follows from `ProPInvariantsExactStatement` (a hypothesis `hP`).

The direct limit over `H` and Harris's quasi-isomorphism (2.6) are not constructed.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe w uR uG uV u v u₁ v₁ u₂ v₂


section RepTrivial

variable {k : Type u} [CommRing k] {Γ : Type v} [Group Γ]

/-- An element acting trivially on a representation acts trivially on every isomorphic
representation. -/
lemma Rep.ρ_eq_id_of_iso {A B : Rep.{w} k Γ} (i : A ≅ B) {g : Γ} (h : A.ρ g = LinearMap.id) :
    B.ρ g = LinearMap.id := by
  ext b
  have := Rep.hom_comm_apply i.hom g (i.inv.hom b)
  rw [h, LinearMap.id_apply] at this
  have h₂ : i.hom.hom (i.inv.hom b) = b := congrArg (fun f : B ⟶ B => f.hom b) i.inv_hom_id
  rw [h₂] at this
  exact this.symm

/-- Every element acts trivially on a zero representation. -/
lemma Rep.ρ_eq_id_of_isZero {A : Rep.{w} k Γ} (hA : IsZero A) (g : Γ) :
    A.ρ g = LinearMap.id := by
  have := (_root_.Rep.isZero_iff (M := A)).1 hA
  ext a
  exact Subsingleton.elim _ _

end RepTrivial

section SmoothZero

variable {R : Type uR} [CommRing R] {H : Type uG} [Group H] [TopologicalSpace H]

/-- A zero representation is smooth. -/
lemma Rep.isSmooth_of_isZero {A : Rep.{uV} R H} (hA : IsZero A) : IsSmooth A.ρ := by
  have := (_root_.Rep.isZero_iff (M := A)).1 hA
  exact fun _ => ⟨⊤, fun _ => Subsingleton.elim _ _⟩

/-- A representation isomorphic to a smooth representation is smooth. -/
lemma Rep.isSmooth_of_iso {A B : Rep.{uV} R H} (i : A ≅ B) (hB : IsSmooth B.ρ) :
    IsSmooth A.ρ := by
  intro v
  obtain ⟨K, hK⟩ := hB (i.hom.hom v)
  refine ⟨K, fun k => ?_⟩
  have h₁ := Rep.hom_comm_apply i.inv (k : H) (i.hom.hom v)
  have h₂ : ∀ a : A, i.inv.hom (i.hom.hom a) = a := fun a =>
    congrArg (fun f : A ⟶ A => f.hom a) i.hom_inv_id
  rw [show B.ρ (k : H) (i.hom.hom v) = i.hom.hom v from hK k, h₂] at h₁
  exact h₁.symm

end SmoothZero

section ProPInclusion

open HomologicalComplex

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {p : ℕ} {H : Subgroup G} [H.Normal]

/-- Given `ProPInvariantSubcomplexStatement`, for a normal pro-`p` subgroup `H` and `p`
invertible in `R`, the inclusion of the inflated `H`-invariants of an `ℕ`-graded complex of
representations of `G` is a quasi-isomorphism, provided that every degree restricted to `H` is
smooth and that `H` acts trivially on the cohomology. -/
theorem quasiIso_quotientInvariantsInclusion_app
    (hS : ProPInvariantSubcomplexStatement.{uG, uR, uV}) (hH : IsProPSubgroup p H)
    (hR : IsUnit (p : R)) (L : CochainComplex (Rep.{uV} R G) ℕ)
    (hL : ∀ n, IsSmooth ((Rep.resFunctor H.subtype).obj (L.X n)).ρ)
    (htriv : ∀ n (h : H), (L.homology n).ρ h = LinearMap.id) :
    QuasiIso ((NatTrans.mapHomologicalComplex (quotientInvariantsInclusion R H)
      (ComplexShape.up ℕ)).app L) := by
  have := hH.compactSpace
  have := hH.totallyDisconnectedSpace
  let e := ComplexShape.embeddingUpNat
  let res : Rep.{uV} R G ⥤ Rep.{uV} R H := Rep.resFunctor.{uV} H.subtype
  have : PreservesFiniteLimits res := inferInstanceAs
    (PreservesFiniteLimits (Rep.resFunctor.{uV} (k := R) H.subtype))
  have : PreservesFiniteColimits res := inferInstanceAs
    (PreservesFiniteColimits (Rep.resFunctor.{uV} (k := R) H.subtype))
  let C' := (res.mapHomologicalComplex (ComplexShape.up ℕ)).obj L
  have hsmooth : ∀ i : ℤ, IsSmooth ((C'.extend e).X i).ρ := fun i => by
    by_cases hi : ∃ n : ℕ, e.f n = i
    · obtain ⟨n, hn⟩ := hi
      exact Rep.isSmooth_of_iso (C'.extendXIso e hn) (hL n)
    · exact Rep.isSmooth_of_isZero (C'.isZero_extend_X e i fun n hn => hi ⟨n, hn⟩)
  have htriv' : ∀ (q : ℤ) (h : H), ((C'.extend e).homology q).ρ h = LinearMap.id :=
    fun q h => by
      by_cases hq : ∃ n : ℕ, e.f n = q
      · obtain ⟨n, hn⟩ := hq
        exact Rep.ρ_eq_id_of_iso
          (((L.sc n).mapHomologyIso res).symm ≪≫ (C'.extendHomologyIso e hn).symm) (htriv n h)
      · exact Rep.ρ_eq_id_of_isZero (((C'.extend e).exactAt_iff_isZero_homology q).1
          (C'.extend_exactAt e q fun n hn => hq ⟨n, hn⟩)) h
  have h₁ := hS p hH.prime H hH.isPGroup R hR (C'.extend e) hsmooth htriv'
  have h₂ := (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk (extendMapIso e _ C')
    (extendMapIso e _ C') (extendMapIso_hom_app e (invariantsInclusion R H) C').symm)).1 h₁
  have h₃ := (quasiIso_extendMap_iff _ e).1 h₂
  rw [← quasiIso_map_iff_of_preservesHomology _ (forget₂ (Rep.{uV} R G) (ModuleCat.{uV} R))]
  refine (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk (Iso.refl _) (Iso.refl _) ?_)).1 h₃
  ext n x
  rfl

end ProPInclusion

section Inflation

variable (R : Type uR) [CommRing R] {G : Type uG} [Group G] (H : Subgroup G) [H.Normal]

/-- Inflation of representations along `G ⟶ G ⧸ H`: restriction along `QuotientGroup.mk' H`. -/
abbrev Rep.quotientInflation : Rep.{uV} R (G ⧸ H) ⥤ Rep.{uV} R G :=
  Rep.resFunctor.{uV} (k := R) (QuotientGroup.mk' H)

instance : PreservesFiniteLimits (Rep.quotientInflation.{uR, uG, uV} R H) :=
  inferInstanceAs (PreservesFiniteLimits (Rep.resFunctor.{uV} (k := R) (QuotientGroup.mk' H)))

instance : PreservesFiniteColimits (Rep.quotientInflation.{uR, uG, uV} R H) :=
  inferInstanceAs (PreservesFiniteColimits (Rep.resFunctor.{uV} (k := R) (QuotientGroup.mk' H)))

end Inflation

namespace DivisibleSystem

section ExtendSystem

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {ℓ : ℕ} (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- A morphism of `ℓ`-divisible systems mapped by an exact functor: `mapFunctor` on morphisms,
with source and target written as `DivisibleSystem.map`. -/
def mapHom {T T' : DivisibleSystem A ℓ} (f : T ⟶ T') : T.map F ⟶ T'.map F :=
  (mapFunctor A ℓ F).map f

lemma mapHom_tower_app {T T' : DivisibleSystem A ℓ} (f : T ⟶ T') (m : ℕᵒᵖ) :
    (mapHom F f).tower.app m = F.map (f.tower.app m) :=
  rfl

/-- Extending an `ℓ`-divisible system of `ℕ`-graded complexes to `ℤ` commutes with applying an
exact functor degreewise: `extendMapIso` at every level. -/
def extendSystemMapHom (T : DivisibleSystem (CochainComplex A ℕ) ℓ) :
    T.extendSystem.map (F.mapHomologicalComplex (ComplexShape.up ℤ)) ⟶
      (T.map (F.mapHomologicalComplex (ComplexShape.up ℕ))).extendSystem :=
  ⟨{ app := fun m => (extendMapIso ComplexShape.embeddingUpNat F (T.tower.obj m)).hom
     naturality := fun _ _ φ => extendMapIso_hom_naturality _ F (T.tower.map φ) },
    fun h => extendMapIso_hom_naturality _ F (T.inclusion h)⟩

lemma extendSystemMapHom_tower_app (T : DivisibleSystem (CochainComplex A ℕ) ℓ) (m : ℕ) :
    (extendSystemMapHom F T).tower.app (op m) =
      (extendMapIso ComplexShape.embeddingUpNat F (T.obj m)).hom :=
  rfl

instance isIso_extendSystemMapHom (T : DivisibleSystem (CochainComplex A ℕ) ℓ) :
    IsIso (extendSystemMapHom F T) := by
  have : ∀ m, IsIso ((extendSystemMapHom F T).tower.app m) := fun m =>
    inferInstanceAs (IsIso (extendMapIso ComplexShape.embeddingUpNat F (T.tower.obj m)).hom)
  exact isIso_of_isIso_tower_app _

/-- `extendSystemMapHom` as an isomorphism of `ℓ`-divisible systems. -/
def extendSystemMapIso (T : DivisibleSystem (CochainComplex A ℕ) ℓ) :
    T.extendSystem.map (F.mapHomologicalComplex (ComplexShape.up ℤ)) ≅
      (T.map (F.mapHomologicalComplex (ComplexShape.up ℕ))).extendSystem :=
  asIso (extendSystemMapHom F T)

variable {T₀ : DivisibleSystem (CochainComplex A ℤ) ℓ} {T : DivisibleSystem (CochainComplex A ℕ) ℓ}
  {T' : DivisibleSystem (CochainComplex B ℕ) ℓ}

/-- For `f : T₀ ⟶ T.extendSystem` and `g : T.map F ⟶ T'` (with `F` applied degreewise), the
composite of `f` mapped by `F`, `extendSystemMapHom` and the extension of `g` to `ℤ`. -/
def extendSystemComparison (f : T₀ ⟶ T.extendSystem)
    (g : T.map (F.mapHomologicalComplex (ComplexShape.up ℕ)) ⟶ T') :
    T₀.map (F.mapHomologicalComplex (ComplexShape.up ℤ)) ⟶ T'.extendSystem :=
  mapHom (F.mapHomologicalComplex (ComplexShape.up ℤ)) f ≫ extendSystemMapHom F T ≫
    mapHom (ComplexShape.embeddingUpNat.extendFunctor B) g

lemma extendSystemComparison_tower_app (f : T₀ ⟶ T.extendSystem)
    (g : T.map (F.mapHomologicalComplex (ComplexShape.up ℕ)) ⟶ T') (m : ℕᵒᵖ) :
    (extendSystemComparison F f g).tower.app m =
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (f.tower.app m) ≫
        (extendMapIso ComplexShape.embeddingUpNat F (T.tower.obj m)).hom ≫
          HomologicalComplex.extendMap (g.tower.app m) ComplexShape.embeddingUpNat :=
  rfl

/-- `extendSystemComparison F f g` is a quasi-isomorphism at every level at which `f` and `g`
are. -/
theorem quasiIso_extendSystemComparison_tower_app (f : T₀ ⟶ T.extendSystem)
    (g : T.map (F.mapHomologicalComplex (ComplexShape.up ℕ)) ⟶ T') (m : ℕᵒᵖ)
    (hf : QuasiIso (f.tower.app m)) (hg : QuasiIso (g.tower.app m)) :
    QuasiIso ((extendSystemComparison F f g).tower.app m) := by
  rw [extendSystemComparison_tower_app]
  have : F.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels F
  have h₁ : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (f.tower.app m)) :=
    inferInstance
  have h₂ : QuasiIso (extendMapIso ComplexShape.embeddingUpNat F (T.tower.obj m)).hom :=
    inferInstance
  have h₃ := (HomologicalComplex.quasiIso_extendMap_iff (g.tower.app m)
    ComplexShape.embeddingUpNat).2 hg
  exact quasiIso_comp _ _ (hφ := h₁) (hφ' := quasiIso_comp _ _ (hφ := h₂) (hφ' := h₃))

end ExtendSystem

section Inclusion

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {ℓ : ℕ}
  (K : DivisibleSystem (CochainComplex (SmoothRep.{uR, uG, uV} R G) ℕ) ℓ)
  (H : Subgroup G) [H.Normal]

/-- Each level of `quotientInvariantsComplexesInclusion` is the inclusion of the inflated
`H`-invariants of the underlying complex of representations. -/
lemma quotientInvariantsComplexesInclusion_tower_app_eq
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q)))
    (m : ℕ) :
    (K.quotientInvariantsComplexesInclusion H hK).tower.app (op m) =
      (NatTrans.mapHomologicalComplex (quotientInvariantsInclusion R H)
        (ComplexShape.up ℕ)).app (K.toRepComplexes.obj m) :=
  HomologicalComplex.hom_ext _ _ fun _ => Category.comp_id _

variable [IsTopologicalGroup G] {H}

/-- Given `ProPInvariantSubcomplexStatement`, for a normal pro-`p` subgroup `H` and `p`
invertible in `R`, the inclusion of the inflated `H`-invariants is a quasi-isomorphism at every
level `m` at which `H` acts trivially on the cohomology (Harris 1999, p.305). -/
theorem quasiIso_quotientInvariantsComplexesInclusion
    (hS : ProPInvariantSubcomplexStatement.{uG, uR, uV}) {p : ℕ} (hH : IsProPSubgroup p H)
    (hR : IsUnit (p : R))
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q)))
    (m : ℕ) (htriv : ∀ q (h : H), ((K.toRepComplexes.obj m).homology q).ρ h = LinearMap.id) :
    QuasiIso ((K.quotientInvariantsComplexesInclusion H hK).tower.app (op m)) := by
  rw [K.quotientInvariantsComplexesInclusion_tower_app_eq H hK m]
  exact quasiIso_quotientInvariantsInclusion_app hS hH hR _
    (fun n => isSmooth_res_subtype R H ((K.obj m).X n)) htriv

end Inclusion

section Inflation

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {ℓ : ℕ}
  (N : ℕ) (K : DivisibleSystem (CochainComplex (SmoothRep.{uR, uG, max w uR uG} R G) ℕ) ℓ)
  (H : Subgroup G) [H.Normal]

/-- The inflation along `G ⟶ G ⧸ H` of the `H`-invariants system, taken degreewise after forming
the system, compared with `inflatedQuotientInvariantsComplexes` (which applies the composite
functor): the components are the canonical isomorphisms `Functor.mapHomologicalComplexCompIso`,
the identity in every degree. -/
def inflateQuotientInvariantsComplexesHom
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q))) :
    (K.quotientInvariantsComplexes H hK).map
        ((Rep.quotientInflation.{uR, uG, max w uR uG} R H).mapHomologicalComplex
          (ComplexShape.up ℕ)) ⟶
      K.inflatedQuotientInvariantsComplexes H hK :=
  ⟨Functor.whiskerLeft K.tower (Functor.mapHomologicalComplexCompIso
      (Iso.refl (smoothQuotientInvariants R H ⋙ Rep.quotientInflation R H)) _).hom,
    fun _ => HomologicalComplex.hom_ext _ _ fun _ =>
      (Category.comp_id _).trans (Category.id_comp _).symm⟩

instance isIso_inflateQuotientInvariantsComplexesHom_tower_app
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q))) (m : ℕᵒᵖ) :
    IsIso ((inflateQuotientInvariantsComplexesHom.{w, uR, uG} K H hK).tower.app m) :=
  inferInstanceAs (IsIso ((Functor.mapHomologicalComplexCompIso
    (Iso.refl (smoothQuotientInvariants R H ⋙ Rep.quotientInflation.{uR, uG, max w uR uG} R H))
      (ComplexShape.up ℕ)).hom.app (K.tower.obj m)))

variable [H.FiniteIndex]

/-- The inflation along `G ⟶ G ⧸ H` of Harris's `C_m^{•,H}` (`quotientInvariantsTotalSystem`,
rows `q < N`), as an `ℓ`-divisible system of `ℤ`-graded complexes of representations of `G`. -/
abbrev inflatedQuotientInvariantsTotalSystem
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q))) :
    DivisibleSystem (CochainComplex (Rep.{max w uR uG} R G) ℤ) ℓ :=
  (quotientInvariantsTotalSystem.{w, uR, uG} N K H hK).map
    ((Rep.quotientInflation.{uR, uG, max w uR uG} R H).mapHomologicalComplex (ComplexShape.up ℤ))

/-- The `G`-equivariant comparison from the inflated `C_m^{•,H}` to the underlying complexes of
representations of `K` extended to `ℤ`, for `K` vanishing in degrees `q ≥ N`: the
`extendSystemComparison` of `quotientInvariantsTotalSystemToExtend` and of
`inflateQuotientInvariantsComplexesHom` followed by the inclusion of the inflated
`H`-invariants. -/
abbrev quotientInvariantsTotalSystemToRepExtend
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q)))
    (hN : ∀ m q, N ≤ q → IsZero ((K.obj m).X q)) :
    inflatedQuotientInvariantsTotalSystem.{w, uR, uG} N K H hK ⟶
      K.toRepComplexes.extendSystem :=
  extendSystemComparison (Rep.quotientInflation.{uR, uG, max w uR uG} R H)
    (quotientInvariantsTotalSystemToExtend.{w, uR, uG} N K H hK hN)
    (inflateQuotientInvariantsComplexesHom.{w, uR, uG} K H hK ≫
      K.quotientInvariantsComplexesInclusion H hK)

variable [IsTopologicalGroup G] {H}

/-- Given `ProPInvariantSubcomplexStatement`, for a normal pro-`p` subgroup `H` of finite index
and `p` invertible in `R`, the comparison `quotientInvariantsTotalSystemToRepExtend` is a
quasi-isomorphism at every level `m` at which `H` acts trivially on the cohomology. -/
theorem quasiIso_quotientInvariantsTotalSystemToRepExtend
    (hS : ProPInvariantSubcomplexStatement.{uG, uR, max w uR uG}) {p : ℕ}
    (hH : IsProPSubgroup p H) (hR : IsUnit (p : R))
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q)))
    (hN : ∀ m q, N ≤ q → IsZero ((K.obj m).X q)) (m : ℕ)
    (htriv : ∀ q (h : H), ((K.toRepComplexes.obj m).homology q).ρ h = LinearMap.id) :
    QuasiIso ((quotientInvariantsTotalSystemToRepExtend.{w, uR, uG} N K H hK hN).tower.app
      (op m)) := by
  have hg : QuasiIso ((inflateQuotientInvariantsComplexesHom.{w, uR, uG} K H hK ≫
      K.quotientInvariantsComplexesInclusion H hK).tower.app (op m)) := by
    have := K.quasiIso_quotientInvariantsComplexesInclusion hS hH hR hK m htriv
    rw [comp_tower, NatTrans.comp_app]
    infer_instance
  have hf := quasiIso_quotientInvariantsTotalSystemToExtend.{w, uR, uG} N K H hK hN m
  rw [extendSystemComparison_tower_app]
  have : (Rep.quotientInflation.{uR, uG, max w uR uG} R H).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  have h₁ : QuasiIso (((Rep.quotientInflation.{uR, uG, max w uR uG} R H).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
        ((quotientInvariantsTotalSystemToExtend.{w, uR, uG} N K H hK hN).tower.app (op m))) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology (hφ := hf) _ _
  have h₂ : QuasiIso (extendMapIso ComplexShape.embeddingUpNat
      (Rep.quotientInflation.{uR, uG, max w uR uG} R H)
        ((K.quotientInvariantsComplexes H hK).tower.obj (op m))).hom := inferInstance
  have h₃ := (HomologicalComplex.quasiIso_extendMap_iff
      ((inflateQuotientInvariantsComplexesHom.{w, uR, uG} K H hK ≫
        K.quotientInvariantsComplexesInclusion H hK).tower.app (op m))
        ComplexShape.embeddingUpNat).2 hg
  exact quasiIso_comp _ _ (hφ := h₁) (hφ' := quasiIso_comp _ _ (hφ := h₂) (hφ' := h₃))

end Inflation

section ProP

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {ℓ : ℕ} {p : ℕ} {H : Subgroup G} [H.Normal]

/-- Given `ProPInvariantsExactStatement` and `ProPInvariantSubcomplexStatement`, for a normal
pro-`p` subgroup `H` and `p` invertible in `R`, the inclusion
`proPQuotientInvariantsComplexesInclusion` of the inflated `H`-invariants is a
quasi-isomorphism at every level `m` at which `H` acts trivially on the cohomology. -/
theorem quasiIso_proPQuotientInvariantsComplexesInclusion
    (hP : ProPInvariantsExactStatement.{uG, uR, uV})
    (hS : ProPInvariantSubcomplexStatement.{uG, uR, uV}) (hH : IsProPSubgroup p H)
    (hR : IsUnit (p : R)) (K : DivisibleSystem (CochainComplex (SmoothRep.{uR, uG, uV} R G) ℕ) ℓ)
    (m : ℕ) (htriv : ∀ q (h : H), ((K.toRepComplexes.obj m).homology q).ρ h = LinearMap.id) :
    QuasiIso ((K.proPQuotientInvariantsComplexesInclusion hP hH hR).tower.app (op m)) :=
  K.quasiIso_quotientInvariantsComplexesInclusion hS hH hR _ m htriv

variable [H.FiniteIndex] (N : ℕ) (hP : ProPInvariantsExactStatement.{uG, uR, max w uR uG})
  (hH : IsProPSubgroup p H) (hR : IsUnit (p : R))
  (K : DivisibleSystem (CochainComplex (SmoothRep.{uR, uG, max w uR uG} R G) ℕ) ℓ)

/-- The comparison `quotientInvariantsTotalSystemToRepExtend` for a normal pro-`p` subgroup `H`
of finite index and `p` invertible in `R`, given `ProPInvariantsExactStatement`. -/
abbrev proPQuotientInvariantsTotalSystemToRepExtend
    (hN : ∀ m q, N ≤ q → IsZero ((K.obj m).X q)) :
    inflatedQuotientInvariantsTotalSystem.{w, uR, uG} N K H
        (epi_smoothQuotientInvariants_map_projection_f.{uR, uG, max w uR uG} hP hH hR K) ⟶
      K.toRepComplexes.extendSystem :=
  quotientInvariantsTotalSystemToRepExtend.{w, uR, uG} N K H
    (epi_smoothQuotientInvariants_map_projection_f.{uR, uG, max w uR uG} hP hH hR K) hN

/-- Given `ProPInvariantsExactStatement` and `ProPInvariantSubcomplexStatement`, for a normal
pro-`p` subgroup `H` of finite index and `p` invertible in `R`, the comparison
`proPQuotientInvariantsTotalSystemToRepExtend` is a quasi-isomorphism at every level `m` at
which `H` acts trivially on the cohomology. -/
theorem quasiIso_proPQuotientInvariantsTotalSystemToRepExtend
    (hS : ProPInvariantSubcomplexStatement.{uG, uR, max w uR uG})
    (hN : ∀ m q, N ≤ q → IsZero ((K.obj m).X q)) (m : ℕ)
    (htriv : ∀ q (h : H), ((K.toRepComplexes.obj m).homology q).ρ h = LinearMap.id) :
    QuasiIso ((proPQuotientInvariantsTotalSystemToRepExtend.{w, uR, uG} N hP hH hR K hN).tower.app
      (op m)) :=
  quasiIso_quotientInvariantsTotalSystemToRepExtend.{w, uR, uG} N K hS hH hR _ hN m htriv

end ProP

end DivisibleSystem

end Langlands.Cohomology
