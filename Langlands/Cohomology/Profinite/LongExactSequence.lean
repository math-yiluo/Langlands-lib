import Langlands.Cohomology.Profinite.Functoriality
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# The long exact sequence of cohomology

A short exact sequence `0 → A → B → C → 0` of smooth representations gives a short exact
sequence of complexes of locally constant cochains (a locally constant cochain with values in
`C` lifts to a locally constant cochain with values in `B` by composing with any set-theoretic
section). Hence the connecting maps `δ hS i j hij : Hⁱ(G, C) ⟶ Hʲ(G, A)` (`j = i + 1`) and the
exactness of the long exact sequence at the three places (`cohomology_exact₁`, `exact₂`,
`exact₃`), with naturality in the short exact sequence (`δ_naturality`), and compatibility with
the maps along continuous homomorphisms (`δ_comp_map`), in particular with restriction
(`δ_comp_res`) and inflation (`δ_comp_infl`).

References: J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition
(Springer 2008; corrected printing 2013), chapter I, §3, Theorem (1.3.2), p. 27; J.-P. Serre,
*Galois Cohomology* (English translation of *Cohomologie galoisienne*, Springer 1997; corrected
printing 2002), chapter I, §2.2, p. 11 (the `H^q(G, ·)` are the derived functors of `A ↦ A^G` on
discrete modules).
-/

namespace Langlands.ProfiniteCohomology

open CategoryTheory ShortComplex

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section

variable (S : ShortComplex (Rep.{u} k G)) [IsSmoothRep S.X₁] [IsSmoothRep S.X₂]
  [IsSmoothRep S.X₃]

noncomputable def cochainsShortComplex : ShortComplex (CochainComplex (ModuleCat k) ℕ) :=
  ShortComplex.mk (cochainsMap (.id G) S.f) (cochainsMap (.id G) S.g) (by
    rw [← cochainsMap_id_comp, S.zero]; exact cochainsMap_id_zero)

variable {S}

theorem cochainsShortComplex_shortExact (hS : S.ShortExact) :
    (cochainsShortComplex S).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => {
    exact := by
      rw [ShortComplex.moduleCat_exact_iff]
      intro x₂ hx₂
      let c : locallyConstantCochains S.X₂ i := x₂
      have hexact := hS.exact.map (forget₂ (Rep.{u} k G) (ModuleCat k))
      rw [ShortComplex.moduleCat_exact_iff] at hexact
      have hval : ∀ σ, S.g.hom (c.1 σ) = 0 := fun σ =>
        congrArg (fun x : locallyConstantCochains S.X₃ i => x.1 σ) hx₂
      let t : S.X₂ → S.X₁ := Function.invFun S.f.hom
      have ht : ∀ σ, S.f.hom (t (c.1 σ)) = c.1 σ := fun σ =>
        Function.invFun_eq (hexact (c.1 σ) (hval σ))
      refine ⟨(⟨t ∘ c.1, (mem_locallyConstantCochains _ _).2 (IsLocallyConstant.comp c.2 t)⟩ :
        locallyConstantCochains S.X₁ i), ?_⟩
      apply Subtype.ext
      funext σ
      exact ht σ
    mono_f := by
      have := hS.mono_f
      exact (inferInstance : Mono ((cochainsMap (.id G) S.f).f i))
    epi_g := by
      have := hS.epi_g
      exact (inferInstance : Epi ((cochainsMap (.id G) S.g).f i)) }

variable (hS : S.ShortExact)

noncomputable def δ (i j : ℕ) (hij : i + 1 = j) : cohomology S.X₃ i ⟶ cohomology S.X₁ j :=
  (cochainsShortComplex_shortExact hS).δ i j hij

@[reassoc (attr := simp)]
theorem δ_comp (i j : ℕ) (hij : i + 1 = j) : δ hS i j hij ≫ map (.id G) S.f j = 0 :=
  (cochainsShortComplex_shortExact hS).δ_comp i j hij

@[reassoc (attr := simp)]
theorem comp_δ (i j : ℕ) (hij : i + 1 = j) : map (.id G) S.g i ≫ δ hS i j hij = 0 :=
  (cochainsShortComplex_shortExact hS).comp_δ i j hij

theorem map_f_comp_g (i : ℕ) : map (.id G) S.f i ≫ map (.id G) S.g i = 0 := by
  rw [← map_id_comp, S.zero, map_id_zero]

theorem cohomology_exact₁ (i j : ℕ) (hij : i + 1 = j) :
    (ShortComplex.mk (δ hS i j hij) (map (.id G) S.f j) (δ_comp hS i j hij)).Exact :=
  (cochainsShortComplex_shortExact hS).homology_exact₁ i j hij

include hS in

theorem cohomology_exact₂ (i : ℕ) :
    (ShortComplex.mk (map (.id G) S.f i) (map (.id G) S.g i)
      (map_f_comp_g i)).Exact :=
  (cochainsShortComplex_shortExact hS).homology_exact₂ i

theorem cohomology_exact₃ (i j : ℕ) (hij : i + 1 = j) :
    (ShortComplex.mk (map (.id G) S.g i) (δ hS i j hij) (comp_δ hS i j hij)).Exact :=
  (cochainsShortComplex_shortExact hS).homology_exact₃ i j hij

end

section Naturality

variable {S₁ S₂ : ShortComplex (Rep.{u} k G)} [IsSmoothRep S₁.X₁] [IsSmoothRep S₁.X₂]
  [IsSmoothRep S₁.X₃] [IsSmoothRep S₂.X₁] [IsSmoothRep S₂.X₂] [IsSmoothRep S₂.X₃]

noncomputable def cochainsShortComplexMap (φ : S₁ ⟶ S₂) :
    cochainsShortComplex S₁ ⟶ cochainsShortComplex S₂ where
  τ₁ := cochainsMap (.id G) φ.τ₁
  τ₂ := cochainsMap (.id G) φ.τ₂
  τ₃ := cochainsMap (.id G) φ.τ₃
  comm₁₂ := by
    change cochainsMap (.id G) φ.τ₁ ≫ cochainsMap (.id G) S₂.f = cochainsMap (.id G) S₁.f ≫ cochainsMap (.id G) φ.τ₂
    rw [← cochainsMap_id_comp, ← cochainsMap_id_comp, φ.comm₁₂]
  comm₂₃ := by
    change cochainsMap (.id G) φ.τ₂ ≫ cochainsMap (.id G) S₂.g = cochainsMap (.id G) S₁.g ≫ cochainsMap (.id G) φ.τ₃
    rw [← cochainsMap_id_comp, ← cochainsMap_id_comp, φ.comm₂₃]

theorem δ_naturality (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (i j : ℕ)
    (hij : i + 1 = j) :
    δ hS₁ i j hij ≫ map (.id G) φ.τ₁ j = map (.id G) φ.τ₃ i ≫ δ hS₂ i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality (cochainsShortComplexMap φ)
    (cochainsShortComplex_shortExact hS₁) (cochainsShortComplex_shortExact hS₂) i j hij

end Naturality

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

section General

variable {S : ShortComplex (Rep.{u} k G)} [IsSmoothRep S.X₁] [IsSmoothRep S.X₂]
  [IsSmoothRep S.X₃] {T : ShortComplex (Rep.{u} k H)} [IsSmoothRep T.X₁]
  [IsSmoothRep T.X₂] [IsSmoothRep T.X₃] (φ : H →ₜ* G)
  (α : S.map (Rep.resFunctor (φ : H →* G)) ⟶ T)

noncomputable def cochainsShortComplexMapAlong :
    cochainsShortComplex S ⟶ cochainsShortComplex T where
  τ₁ := cochainsMap (A := S.X₁) φ α.τ₁
  τ₂ := cochainsMap (A := S.X₂) φ α.τ₂
  τ₃ := cochainsMap (A := S.X₃) φ α.τ₃
  comm₁₂ := by
    ext n x : 3
    apply Subtype.ext
    funext h
    exact congrArg (fun ψ => ψ.hom (((cochainsι S.X₁).f n).hom x (⇑φ ∘ h))) α.comm₁₂
  comm₂₃ := by
    ext n x : 3
    apply Subtype.ext
    funext h
    exact congrArg (fun ψ => ψ.hom (((cochainsι S.X₂).f n).hom x (⇑φ ∘ h))) α.comm₂₃

@[reassoc]
theorem δ_comp_map (hS : S.ShortExact) (hT : T.ShortExact) (i j : ℕ)
    (hij : i + 1 = j) :
    δ hS i j hij ≫ map (A := S.X₁) φ α.τ₁ j =
      map (A := S.X₃) φ α.τ₃ i ≫ δ hT i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality (cochainsShortComplexMapAlong φ α)
    (cochainsShortComplex_shortExact hS) (cochainsShortComplex_shortExact hT) i j hij

end General

section Restriction

variable (X : ShortComplex (Rep.{u} k G)) [IsSmoothRep X.X₁] [IsSmoothRep X.X₂]
  [IsSmoothRep X.X₃] (U : Subgroup G)

instance isSmoothRep_map_res_X₁ : IsSmoothRep (X.map (Rep.resFunctor U.subtype)).X₁ :=
  isSmoothRep_res_subtype X.X₁ U

instance isSmoothRep_map_res_X₂ : IsSmoothRep (X.map (Rep.resFunctor U.subtype)).X₂ :=
  isSmoothRep_res_subtype X.X₂ U

instance isSmoothRep_map_res_X₃ : IsSmoothRep (X.map (Rep.resFunctor U.subtype)).X₃ :=
  isSmoothRep_res_subtype X.X₃ U

variable {X}

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsSmoothRep X.X₁] [IsSmoothRep X.X₂]
  [IsSmoothRep X.X₃] in

theorem shortExact_map_res (hX : X.ShortExact) : (X.map (Rep.resFunctor U.subtype)).ShortExact :=
  (Rep.shortExact_res U.subtype).2 hX

@[reassoc]
theorem δ_comp_res (hX : X.ShortExact) (i j : ℕ) (hij : i + 1 = j) :
    δ hX i j hij ≫ res X.X₁ U j =
      res X.X₃ U i ≫ δ (shortExact_map_res U hX) i j hij :=
  δ_comp_map (subgroupInclusion U) (𝟙 _) hX
    (shortExact_map_res U hX) i j hij

end Restriction

section Inflation

variable (X : ShortComplex (Rep.{u} k G)) [IsSmoothRep X.X₁] [IsSmoothRep X.X₂]
  [IsSmoothRep X.X₃] (N : Subgroup G) [N.Normal]

omit [TopologicalSpace G] [IsTopologicalGroup G] in

instance quotientToInvariantsFunctor_preservesZeroMorphisms :
    (Rep.quotientToInvariantsFunctor.{u} k N).PreservesZeroMorphisms where
  map_zero _ _ := by
    ext
    rfl

instance isSmoothRep_map_quotientToInvariants_X₁ :
    IsSmoothRep (X.map (Rep.quotientToInvariantsFunctor k N)).X₁ :=
  isSmoothRep_quotientToInvariants X.X₁ N

instance isSmoothRep_map_quotientToInvariants_X₂ :
    IsSmoothRep (X.map (Rep.quotientToInvariantsFunctor k N)).X₂ :=
  isSmoothRep_quotientToInvariants X.X₂ N

instance isSmoothRep_map_quotientToInvariants_X₃ :
    IsSmoothRep (X.map (Rep.quotientToInvariantsFunctor k N)).X₃ :=
  isSmoothRep_quotientToInvariants X.X₃ N

noncomputable def mapQuotientToInvariantsResToSelf :
    (X.map (Rep.quotientToInvariantsFunctor k N)).map (Rep.resFunctor (QuotientGroup.mk' N)) ⟶
      X where
  τ₁ := Rep.ofHom (X.X₁.ρ.quotientToInvariants_lift N)
  τ₂ := Rep.ofHom (X.X₂.ρ.quotientToInvariants_lift N)
  τ₃ := Rep.ofHom (X.X₃.ρ.quotientToInvariants_lift N)
  comm₁₂ := rfl
  comm₂₃ := rfl

variable {X}

@[reassoc]
theorem δ_comp_infl (hX : X.ShortExact)
    (hXN : (X.map (Rep.quotientToInvariantsFunctor k N)).ShortExact) (i j : ℕ)
    (hij : i + 1 = j) :
    δ hXN i j hij ≫ infl X.X₁ N j = infl X.X₃ N i ≫ δ hX i j hij :=
  δ_comp_map (quotientMap N)
    (mapQuotientToInvariantsResToSelf X N) hXN hX i j hij

end Inflation

end Langlands.ProfiniteCohomology
