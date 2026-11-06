import Langlands.Cohomology.DivisibleSystem.ReductionSequence
import Langlands.Cohomology.DivisibleSystem.ConstantInverseLimit

/-!
# Reduction sequences for `ℓ`-adic limits of truncated Godement section systems

Milne, *Étale Cohomology* (1980), Ch. V, §1, Lemma 1.11, printed p.165: for an `l`-adic sheaf
`F = (F_n)` with flat levels and finite cohomology there are exact sequences
`0 → H^r(X_et, F)^(l^n) → H^r(X_et, F_n) → H^{r+1}(X_et, F)_{l^n} → 0`, where
`H^r(X, F) = lim_n H^r(X, F_n)` (p.164). Harris, *Galois properties of cohomological automorphic
forms on GL(n)*, §2, pp.305–306, builds the `ℓ`-divisible systems `G_m^•(U)` of sections of the
truncated resolutions `G_m^• = τ^{≤D+1}(F_m^•)` and identifies the cohomology of their inverse
limit with `lim_m H^q` (Lemma 2.8).

This module applies the published reduction sequences (`ReductionSequence`) to the `ℓ`-adic limit
`adicLimit K` of an `ℓ`-divisible system `K` of `ℕ`-graded complexes, and then to Harris's
truncated smooth Godement section systems:

* `comp_eq_zero_of_iso`, `cokernelKernelShortComplexIso`: transport of a vanishing composite and
  of `cokernelKernelShortComplex` along isomorphisms commuting with the maps.
* `adicReductionSequence`, `adicReductionSequence_shortExact`:
  `0 ⟶ H^n(adicLimit K) / ℓ ^ r ⟶ H^n(K r) ⟶ H^{n+1}(adicLimit K)[ℓ ^ r] ⟶ 0`, given short
  exactness `hS` of `0 ⟶ lim ⟶ lim ⟶ K r ⟶ 0` for the extended system.
* `adicLevelReductionSequence`, `adicLevelReductionSequence_shortExact`: the same with
  `lim_m H^n(K m)` in place of `H^n(adicLimit K)`, when the published `adicLimitComparison` is an
  isomorphism in degrees `n` and `n + 1`; `adicLevelReductionSequence_shortExact_of_finite` and
  `adicLevelReductionSequence_shortExact_rep` for complexes of modules and of representations
  with finite cohomology, given Worker 3's `FiniteCohomologyInverseLimitStatement`.
* `smoothGodementReductionSequence`, `smoothGodementReductionSequence_shortExact`: for the
  truncated smooth Godement section system and `n ≤ D`,
  `0 ⟶ (lim_m H^n(Φ(F_m^•))) / ℓ ^ r ⟶ H^n(Φ(F_r^•)) ⟶ (lim_m H^{n+1}(Φ(F_m^•)))[ℓ ^ r] ⟶ 0`,
  through `smoothGodementTruncatedSectionsLevelHomologyIso` and the published
  `smoothGodementTruncatedSectionsAdicCohomologyIso`;
  `smoothGodementReductionSequence_shortExact_of_finite` and
  `smoothGodementReductionSequence_shortExact_rep` for sections functors with values in modules
  and in representations. They apply to the published constant systems, which are abbreviations
  of the smooth one.

The short exactness of `0 ⟶ lim ⟶ lim ⟶ K r ⟶ 0` (proved for modules and representations in the
published `ReductionSequence`), the comparison isomorphisms or
`FiniteCohomologyInverseLimitStatement` with finite cohomology, the exactness of the degree-zero
smooth Godement functor and the surjectivity of the sections functors on the projections are
explicit hypotheses. The statements and proofs are ours.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe w u v u' v'

section FourTermIso

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- If `f ≫ g = 0` and isomorphisms `eX`, `eY`, `eZ` intertwine `f, g` with `f', g'`, then
`f' ≫ g' = 0`. -/
lemma comp_eq_zero_of_iso {X Y Z X' Y' Z' : C} {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'}
    {g' : Y' ⟶ Z'} (eX : X ≅ X') (eY : Y ≅ Y') (eZ : Z ≅ Z') (wf : f ≫ eY.hom = eX.hom ≫ f')
    (wg : g ≫ eZ.hom = eY.hom ≫ g') (hfg : f ≫ g = 0) : f' ≫ g' = 0 := by
  rw [← cancel_epi eX.hom, comp_zero, ← Category.assoc, ← wf, Category.assoc, ← wg,
    ← Category.assoc, hfg, zero_comp]

/-- Isomorphisms between two sequences `A ⟶ B ⟶ X ⟶ D ⟶ E` and `A' ⟶ B' ⟶ X' ⟶ D' ⟶ E'`
commuting with the maps induce an isomorphism of the short complexes
`cokernelKernelShortComplex`. -/
def cokernelKernelShortComplexIso {A B X D E A' B' X' D' E' : C} {f : A ⟶ B} {g : B ⟶ X}
    {δ : X ⟶ D} {h : D ⟶ E} {hfg : f ≫ g = 0} {hgδ : g ≫ δ = 0} {hδh : δ ≫ h = 0}
    {f' : A' ⟶ B'} {g' : B' ⟶ X'} {δ' : X' ⟶ D'} {h' : D' ⟶ E'} {hfg' : f' ≫ g' = 0}
    {hgδ' : g' ≫ δ' = 0} {hδh' : δ' ≫ h' = 0}
    (eA : A ≅ A') (eB : B ≅ B') (eX : X ≅ X') (eD : D ≅ D') (eE : E ≅ E')
    (wf : f ≫ eB.hom = eA.hom ≫ f') (wg : g ≫ eX.hom = eB.hom ≫ g')
    (wδ : δ ≫ eD.hom = eX.hom ≫ δ') (wh : h ≫ eE.hom = eD.hom ≫ h') :
    cokernelKernelShortComplex f g δ h hfg hgδ hδh ≅
      cokernelKernelShortComplex f' g' δ' h' hfg' hgδ' hδh' :=
  ShortComplex.isoMk (cokernel.mapIso f f' eA eB wf) eX (kernel.mapIso h h' eD eE wh)
    (by
      dsimp only [cokernelKernelShortComplex]
      ext
      simp [wg])
    (by
      dsimp only [cokernelKernelShortComplex]
      ext
      simp [wδ])

end FourTermIso

namespace DivisibleSystem

section AdicLimit

variable {E : Type u'} [Category.{v'} E] [Abelian E] [HasLimitsOfShape ℕᵒᵖ E] {ℓ : ℕ}
  {K : DivisibleSystem (CochainComplex E ℕ) ℓ}

variable (K) in
/-- The degree-`n` cohomology of the extension by zero to `ℤ` of level `r` of `K` is that of
level `r` (Mathlib's `extendHomologyIso`). -/
abbrev levelExtendHomologyIso (r n : ℕ) :
    (K.extendSystem.obj r).homology n ≅ (K.obj r).homology n :=
  (extendHomologyNatIso E n).app (K.tower.obj (op r))

/-- The relation `n → n + 1` of the cochain complex shape on `ℤ`, for `n : ℕ`. -/
lemma up_int_rel_natCast (n : ℕ) : (ComplexShape.up ℤ).Rel (n : ℤ) ((n + 1 : ℕ) : ℤ) := by
  simp

variable (K) in
/-- Multiplication by `ℓ ^ r` on `lim_m H^n(K m)` followed by the projection to `H^n(K r)` is
zero. -/
lemma powSMul_comp_levelCohomologyLimit_π (r n : ℕ) :
    powSMul ℓ r (K.levelCohomologyLimit n) ≫
      limit.π (K.tower ⋙ HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n) (op r) =
        0 := by
  rw [← comp_powSMul, powSMul_homology_eq_zero, comp_zero]

variable {r : ℕ} (hS : (reductionShortComplex (limit.cone K.extendSystem.tower) r).ShortExact)
  (n : ℕ)

/-- Milne's sequence for the `ℓ`-adic limit of an `ℓ`-divisible system `K` of `ℕ`-graded
complexes: `H^n(adicLimit K) / ℓ ^ r ⟶ H^n(K r) ⟶ H^{n+1}(adicLimit K)[ℓ ^ r]`, where the first
map is induced by the projection and the second is the connecting map, both through the
identification `levelExtendHomologyIso` of the cohomology of the extended level. -/
def adicReductionSequence : ShortComplex E :=
  cokernelKernelShortComplex (powSMul ℓ r (K.adicLimit.homology n))
    (HomologicalComplex.homologyMap (limit.π K.extendSystem.tower (op r)) n ≫
      (K.levelExtendHomologyIso r n).hom)
    ((K.levelExtendHomologyIso r n).inv ≫ hS.δ n (n + 1 : ℕ) (up_int_rel_natCast n))
    (powSMul ℓ r (K.adicLimit.homology (n + 1 : ℕ)))
    (by
      rw [← Category.assoc, ← homologyMap_powSMul, ← HomologicalComplex.homologyMap_comp]
      erw [powSMul_comp_π (limit.cone K.extendSystem.tower) r]
      rw [HomologicalComplex.homologyMap_zero, zero_comp])
    (by
      rw [Category.assoc, Iso.hom_inv_id_assoc]
      exact hS.comp_δ _ _ _)
    (by
      rw [Category.assoc, ← homologyMap_powSMul]
      erw [hS.δ_comp]
      rw [comp_zero])

/-- `reductionSequence` for the limit cone of the extended system is isomorphic to
`adicReductionSequence`. -/
def reductionSequenceAdicIso :
    reductionSequence hS n (n + 1 : ℕ) (up_int_rel_natCast n) ≅ adicReductionSequence hS n :=
  cokernelKernelShortComplexIso (Iso.refl _) (Iso.refl _) (K.levelExtendHomologyIso r n)
    (Iso.refl _) (Iso.refl _) (by simp) (Category.id_comp _).symm
    ((Category.comp_id _).trans (Iso.hom_inv_id_assoc _ _).symm)
    (by simp)

/-- The projection `H^n(adicLimit K) ⟶ H^n(adicLimit K) / ℓ ^ r` followed by the first map of
`adicReductionSequence` is the map induced by the projection, followed by
`levelExtendHomologyIso`. -/
@[reassoc (attr := simp)]
lemma reductionπ_adicReductionSequence_f :
    reductionπ ℓ (K.adicLimit.homology n) r ≫ (adicReductionSequence hS n).f =
      HomologicalComplex.homologyMap (limit.π K.extendSystem.tower (op r)) n ≫
        (K.levelExtendHomologyIso r n).hom :=
  cokernel.π_desc _ _ _

/-- The second map of `adicReductionSequence` followed by the inclusion of the `ℓ ^ r`-torsion
is the inverse of `levelExtendHomologyIso` followed by the connecting map. -/
@[reassoc (attr := simp)]
lemma adicReductionSequence_g_ι :
    (adicReductionSequence hS n).g ≫ kernel.ι (powSMul ℓ r (K.adicLimit.homology (n + 1 : ℕ))) =
      (K.levelExtendHomologyIso r n).inv ≫ hS.δ n (n + 1 : ℕ) (up_int_rel_natCast n) :=
  kernel.lift_ι _ _ _

/-- Milne, Ch. V, Lemma 1.11, for the `ℓ`-adic limit of an `ℓ`-divisible system of `ℕ`-graded
complexes: `0 ⟶ H^n(adicLimit K) / ℓ ^ r ⟶ H^n(K r) ⟶ H^{n+1}(adicLimit K)[ℓ ^ r] ⟶ 0` is short
exact. -/
theorem adicReductionSequence_shortExact : (adicReductionSequence hS n).ShortExact :=
  ShortComplex.shortExact_of_iso (reductionSequenceAdicIso hS n)
    (reductionSequence_shortExact hS _ _ _)

/-- The map `H^n(adicLimit K) ⟶ H^n(K r)` induced by the projection, followed by the connecting
map `H^n(K r) ⟶ H^{n+1}(adicLimit K)` (both through `levelExtendHomologyIso`), is zero. -/
@[reassoc]
lemma homologyMap_π_comp_δ :
    HomologicalComplex.homologyMap (limit.π K.extendSystem.tower (op r)) n ≫
        (K.levelExtendHomologyIso r n).hom ≫ (K.levelExtendHomologyIso r n).inv ≫
          hS.δ n (n + 1 : ℕ) (up_int_rel_natCast n) = 0 := by
  rw [Iso.hom_inv_id_assoc]
  exact hS.comp_δ _ _ _

variable (hn : IsIso (K.adicLimitComparison n))

include hn in
/-- If `adicLimitComparison` is an isomorphism in degree `n`, the projection
`lim_m H^n(K m) ⟶ H^n(K r)` followed by the connecting map `H^n(K r) ⟶ H^{n+1}(adicLimit K)` and
`adicLimitComparison` in degree `n + 1` is zero. -/
@[reassoc]
lemma levelCohomologyLimit_π_comp_δ :
    limit.π (K.tower ⋙ HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n) (op r) ≫
      (K.levelExtendHomologyIso r n).inv ≫ hS.δ n (n + 1 : ℕ) (up_int_rel_natCast n) ≫
        K.adicLimitComparison (n + 1) = 0 := by
  refine (cancel_epi (K.adicLimitComparison n)).1 ?_
  refine ((adicLimitComparison_π_assoc K n (op r) _).trans ?_).trans comp_zero.symm
  exact (Category.assoc _ _ _).trans ((homologyMap_π_comp_δ_assoc hS n _).trans zero_comp)

/-- The connecting map `H^n(K r) ⟶ H^{n+1}(adicLimit K)` followed by `adicLimitComparison` in
degree `n + 1` and multiplication by `ℓ ^ r` on `lim_m H^{n+1}(K m)` is zero. -/
lemma δ_comp_powSMul_levelCohomologyLimit :
    ((K.levelExtendHomologyIso r n).inv ≫ hS.δ n (n + 1 : ℕ) (up_int_rel_natCast n) ≫
        K.adicLimitComparison (n + 1)) ≫ powSMul ℓ r (K.levelCohomologyLimit (n + 1)) = 0 :=
  ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (((Category.assoc _ _ _).trans
    (congrArg (hS.δ n (n + 1 : ℕ) (up_int_rel_natCast n) ≫ ·)
      ((comp_powSMul ℓ r _).trans (congrArg (· ≫ K.adicLimitComparison (n + 1))
        (homologyMap_powSMul ℓ r K.adicLimit (n + 1 : ℕ)).symm)))).trans
    ((hS.δ_comp_assoc _ _ _ _).trans zero_comp)))).trans comp_zero

/-- Milne's sequence for the `ℓ`-adic limit of an `ℓ`-divisible system `K` of `ℕ`-graded
complexes with `H^r` of the limit replaced by `lim_m H^r(K m)`:
`(lim_m H^n(K m)) / ℓ ^ r ⟶ H^n(K r) ⟶ (lim_m H^{n+1}(K m))[ℓ ^ r]`. The first map is induced by
the projection; the second is the connecting map of `adicReductionSequence` followed by the
comparison `adicLimitComparison` in degree `n + 1`. The comparison in degree `n` is assumed to be
an isomorphism, which is used to show that the composite of the two maps vanishes. -/
def adicLevelReductionSequence : ShortComplex E :=
  cokernelKernelShortComplex (powSMul ℓ r (K.levelCohomologyLimit n))
    (limit.π (K.tower ⋙ HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n) (op r))
    ((K.levelExtendHomologyIso r n).inv ≫ hS.δ n (n + 1 : ℕ) (up_int_rel_natCast n) ≫
      K.adicLimitComparison (n + 1))
    (powSMul ℓ r (K.levelCohomologyLimit (n + 1)))
    (K.powSMul_comp_levelCohomologyLimit_π r n) (levelCohomologyLimit_π_comp_δ hS n hn)
    (δ_comp_powSMul_levelCohomologyLimit hS n)

/-- The projection `lim_m H^n(K m) ⟶ (lim_m H^n(K m)) / ℓ ^ r` followed by the first map of
`adicLevelReductionSequence` is the projection `lim_m H^n(K m) ⟶ H^n(K r)`. -/
@[reassoc (attr := simp)]
lemma reductionπ_adicLevelReductionSequence_f :
    reductionπ ℓ (K.levelCohomologyLimit n) r ≫ (adicLevelReductionSequence hS n hn).f =
      limit.π (K.tower ⋙ HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n) (op r) :=
  cokernel.π_desc _ _ _

/-- The second map of `adicLevelReductionSequence` followed by the inclusion of the
`ℓ ^ r`-torsion is the connecting map followed by `adicLimitComparison` in degree `n + 1`. -/
@[reassoc (attr := simp)]
lemma adicLevelReductionSequence_g_ι :
    (adicLevelReductionSequence hS n hn).g ≫
        kernel.ι (powSMul ℓ r (K.levelCohomologyLimit (n + 1))) =
      (K.levelExtendHomologyIso r n).inv ≫ hS.δ n (n + 1 : ℕ) (up_int_rel_natCast n) ≫
        K.adicLimitComparison (n + 1) :=
  kernel.lift_ι _ _ _

/-- If `adicLimitComparison` is an isomorphism in degrees `n` and `n + 1`, then
`adicReductionSequence` is isomorphic to `adicLevelReductionSequence`. -/
def adicReductionSequenceLevelIso (hn' : IsIso (K.adicLimitComparison (n + 1))) :
    adicReductionSequence hS n ≅ adicLevelReductionSequence hS n hn :=
  cokernelKernelShortComplexIso (asIso (K.adicLimitComparison n))
    (asIso (K.adicLimitComparison n)) (Iso.refl _) (asIso (K.adicLimitComparison (n + 1)))
    (asIso (K.adicLimitComparison (n + 1))) (comp_powSMul ℓ r _).symm
    ((Category.comp_id _).trans (adicLimitComparison_π K n (op r)).symm)
    ((Category.assoc _ _ _).trans (Category.id_comp _).symm) (comp_powSMul ℓ r _).symm

/-- Milne, Ch. V, Lemma 1.11, for the `ℓ`-adic limit of an `ℓ`-divisible system `K` of
`ℕ`-graded complexes, in the form with `H^r = lim_m H^r(K m)`: if `adicLimitComparison` is an
isomorphism in degrees `n` and `n + 1`, then
`0 ⟶ (lim_m H^n(K m)) / ℓ ^ r ⟶ H^n(K r) ⟶ (lim_m H^{n+1}(K m))[ℓ ^ r] ⟶ 0` is short exact. -/
theorem adicLevelReductionSequence_shortExact (hn' : IsIso (K.adicLimitComparison (n + 1))) :
    (adicLevelReductionSequence hS n hn).ShortExact :=
  ShortComplex.shortExact_of_iso (adicReductionSequenceLevelIso hS n hn hn')
    (adicReductionSequence_shortExact hS n)

end AdicLimit

section AdicLimitModules

variable {R : Type u} [CommRing R] {ℓ : ℕ} (hF : FiniteCohomologyInverseLimitStatement.{u, v} R)
  (K : DivisibleSystem (CochainComplex (ModuleCat.{v} R) ℕ) ℓ)
  (hfin : ∀ m n, Finite ((K.obj m).homology n))

include hF hfin in
/-- Milne, Ch. V, Lemma 1.11, for the `ℓ`-adic limit of an `ℓ`-divisible system `K` of
`ℕ`-graded complexes of `R`-modules: given `FiniteCohomologyInverseLimitStatement` and finite
cohomology of the levels, `0 ⟶ (lim_m H^n(K m)) / ℓ ^ r ⟶ H^n(K r) ⟶
(lim_m H^{n+1}(K m))[ℓ ^ r] ⟶ 0` is short exact. -/
theorem adicLevelReductionSequence_shortExact_of_finite (r n : ℕ) :
    (adicLevelReductionSequence (reductionShortComplex_shortExact_moduleCat K.extendSystem r) n
      (isIso_adicLimitComparison_of_finite hF K hfin n)).ShortExact :=
  adicLevelReductionSequence_shortExact _ _ _ (isIso_adicLimitComparison_of_finite hF K hfin _)

end AdicLimitModules

section AdicLimitRep

variable {k : Type u} [CommRing k] {G : Type v} [Monoid G] {ℓ : ℕ}
  (hF : FiniteCohomologyInverseLimitStatement.{u, w} k)
  (K : DivisibleSystem (CochainComplex (Rep.{w} k G) ℕ) ℓ)
  (hfin : ∀ m n, Finite ((K.obj m).homology n))

include hF hfin in
/-- Milne, Ch. V, Lemma 1.11, for the `ℓ`-adic limit of an `ℓ`-divisible system `K` of
`ℕ`-graded complexes of representations: given `FiniteCohomologyInverseLimitStatement` for the
coefficient ring and finite cohomology of the levels, `0 ⟶ (lim_m H^n(K m)) / ℓ ^ r ⟶ H^n(K r) ⟶
(lim_m H^{n+1}(K m))[ℓ ^ r] ⟶ 0` is a short exact sequence of representations. -/
theorem adicLevelReductionSequence_shortExact_rep (r n : ℕ) :
    (adicLevelReductionSequence (reductionShortComplex_shortExact_rep K.extendSystem r) n
      (isIso_adicLimitComparison_rep hF K hfin n)).ShortExact :=
  adicLevelReductionSequence_shortExact _ _ _ (isIso_adicLimitComparison_rep hF K hfin _)

end AdicLimitRep

section SmoothGodement

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ}
  (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)
  (D : ℕ) {E : Type u'} [Category.{v'} E] [Abelian E]
  (Φ : SmoothTopologicalSheaf R G X ⥤ E) [Φ.Additive] [PreservesFiniteLimits Φ]
  (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi (Φ.map ((smoothGodementTermSystem h T q).projection hm)))
  (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi (Φ.map ((smoothGodementResidualSystem h T (D + 1)).projection hm)))

/-- For `n ≤ D + 1`, the inclusion of the truncated smooth Godement section complex `Φ(G_r^•)`
into `Φ(F_r^•)` induces an isomorphism on degree-`n` cohomology. -/
def smoothGodementTruncatedSectionsLevelHomologyIso (r : ℕ) {n : ℕ} (hn : n ≤ D + 1) :
    ((smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).obj r).homology n ≅
      ((smoothGodementSectionsTower h T Φ).obj (op r)).homology n :=
  haveI := smoothGodementTruncatedSectionsTowerHom_quasiIsoAt h T D Φ hterm hres (op r) hn
  asIso (HomologicalComplex.homologyMap
    ((smoothGodementTruncatedSectionsTowerHom h T D Φ hterm hres).app (op r)) n)

/-- `smoothGodementTruncatedSectionsLevelHomologyIso` is the map induced on cohomology by the
inclusion of the truncated section complex. -/
@[simp]
lemma smoothGodementTruncatedSectionsLevelHomologyIso_hom (r : ℕ) {n : ℕ} (hn : n ≤ D + 1) :
    (smoothGodementTruncatedSectionsLevelHomologyIso h T D Φ hterm hres r hn).hom =
      HomologicalComplex.homologyMap
        ((smoothGodementTruncatedSectionsTowerHom h T D Φ hterm hres).app (op r)) n :=
  rfl

variable [HasLimitsOfShape ℕᵒᵖ E]

/-- The projections `lim_m H^n(Φ(G_m^•)) ⟶ H^n(Φ(G_r^•))` and `lim_m H^n(Φ(F_m^•)) ⟶ H^n(Φ(F_r^•))`
commute with `smoothGodementTruncatedSectionsAdicCohomologyIso` and
`smoothGodementTruncatedSectionsLevelHomologyIso`. -/
@[reassoc]
lemma π_smoothGodementTruncatedSectionsLevelHomologyIso_hom (r : ℕ) {n : ℕ} (hn : n ≤ D + 1) :
    limit.π ((smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).tower ⋙
        HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n) (op r) ≫
      (smoothGodementTruncatedSectionsLevelHomologyIso h T D Φ hterm hres r hn).hom =
    (smoothGodementTruncatedSectionsAdicCohomologyIso h T D Φ hterm hres hn).hom ≫
      limit.π (smoothGodementSectionsTower h T Φ ⋙
        HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n) (op r) :=
  (smoothGodementTruncatedSectionsAdicCohomologyIso_hom_π h T D Φ hterm hres hn (op r)).symm

variable {h T D Φ hterm hres} {r : ℕ}
  (hS : (reductionShortComplex (limit.cone
    (smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).extendSystem.tower) r).ShortExact)
  (n : ℕ) (hn : n ≤ D)

/-- The connecting map `H^n(Φ(F_r^•)) ⟶ lim_m H^{n+1}(Φ(F_m^•))` for `n ≤ D`: the connecting map
of `adicReductionSequence` for the truncated section system, transported along
`smoothGodementTruncatedSectionsLevelHomologyIso` in degree `n` and
`smoothGodementTruncatedSectionsAdicCohomologyIso` in degree `n + 1` through
`adicLimitComparison`. -/
def smoothGodementReductionδ :
    ((smoothGodementSectionsTower h T Φ).obj (op r)).homology n ⟶
      limit (smoothGodementSectionsTower h T Φ ⋙
        HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) (n + 1)) :=
  (smoothGodementTruncatedSectionsLevelHomologyIso h T D Φ hterm hres r
      (Nat.le_succ_of_le hn)).inv ≫
    ((smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).levelExtendHomologyIso r n).inv ≫
      hS.δ n (n + 1 : ℕ) (up_int_rel_natCast n) ≫
        (smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).adicLimitComparison (n + 1) ≫
          (smoothGodementTruncatedSectionsAdicCohomologyIso h T D Φ hterm hres
            (Nat.succ_le_succ hn)).hom

/-- The connecting map of `adicLevelReductionSequence` for the truncated section system,
followed by `smoothGodementTruncatedSectionsAdicCohomologyIso` in degree `n + 1`, is
`smoothGodementTruncatedSectionsLevelHomologyIso` followed by `smoothGodementReductionδ`. -/
lemma smoothGodementReductionδ_comm :
    (((smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).levelExtendHomologyIso r n).inv ≫
        hS.δ n (n + 1 : ℕ) (up_int_rel_natCast n) ≫
          (smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).adicLimitComparison (n + 1)) ≫
        (smoothGodementTruncatedSectionsAdicCohomologyIso h T D Φ hterm hres
          (Nat.succ_le_succ hn)).hom =
      (smoothGodementTruncatedSectionsLevelHomologyIso h T D Φ hterm hres r
          (Nat.le_succ_of_le hn)).hom ≫ smoothGodementReductionδ hS n hn :=
  ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).trans
    (Iso.hom_inv_id_assoc _ _).symm

variable (hcmp : IsIso
  ((smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).adicLimitComparison n))

/-- Milne's sequence for Harris's truncated smooth Godement section systems, with cohomology
`lim_m H^n(Φ(F_m^•))`: for `n ≤ D`,
`(lim_m H^n(Φ(F_m^•))) / ℓ ^ r ⟶ H^n(Φ(F_r^•)) ⟶ (lim_m H^{n+1}(Φ(F_m^•)))[ℓ ^ r]`, where the
first map is induced by the projection and the second by `smoothGodementReductionδ`. The
comparison `adicLimitComparison` of the truncated section system in degree `n` is assumed to be
an isomorphism, which is used to show that the composite of the two maps vanishes. -/
def smoothGodementReductionSequence : ShortComplex E :=
  cokernelKernelShortComplex
    (powSMul ℓ r (limit (smoothGodementSectionsTower h T Φ ⋙
      HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n)))
    (limit.π (smoothGodementSectionsTower h T Φ ⋙
      HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n) (op r))
    (smoothGodementReductionδ hS n hn)
    (powSMul ℓ r (limit (smoothGodementSectionsTower h T Φ ⋙
      HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) (n + 1))))
    (comp_eq_zero_of_iso
      (smoothGodementTruncatedSectionsAdicCohomologyIso h T D Φ hterm hres (Nat.le_succ_of_le hn))
      (smoothGodementTruncatedSectionsAdicCohomologyIso h T D Φ hterm hres (Nat.le_succ_of_le hn))
      (smoothGodementTruncatedSectionsLevelHomologyIso h T D Φ hterm hres r
        (Nat.le_succ_of_le hn))
      (comp_powSMul ℓ r _).symm
      (π_smoothGodementTruncatedSectionsLevelHomologyIso_hom h T D Φ hterm hres r _)
      (powSMul_comp_levelCohomologyLimit_π _ r n))
    (comp_eq_zero_of_iso
      (smoothGodementTruncatedSectionsAdicCohomologyIso h T D Φ hterm hres (Nat.le_succ_of_le hn))
      (smoothGodementTruncatedSectionsLevelHomologyIso h T D Φ hterm hres r
        (Nat.le_succ_of_le hn))
      (smoothGodementTruncatedSectionsAdicCohomologyIso h T D Φ hterm hres (Nat.succ_le_succ hn))
      (π_smoothGodementTruncatedSectionsLevelHomologyIso_hom h T D Φ hterm hres r _)
      (smoothGodementReductionδ_comm hS n hn) (levelCohomologyLimit_π_comp_δ hS n hcmp))
    (comp_eq_zero_of_iso
      (smoothGodementTruncatedSectionsLevelHomologyIso h T D Φ hterm hres r
        (Nat.le_succ_of_le hn))
      (smoothGodementTruncatedSectionsAdicCohomologyIso h T D Φ hterm hres (Nat.succ_le_succ hn))
      (smoothGodementTruncatedSectionsAdicCohomologyIso h T D Φ hterm hres (Nat.succ_le_succ hn))
      (smoothGodementReductionδ_comm hS n hn) (comp_powSMul ℓ r _).symm
      (δ_comp_powSMul_levelCohomologyLimit hS n))

/-- The projection `lim_m H^n(Φ(F_m^•)) ⟶ (lim_m H^n(Φ(F_m^•))) / ℓ ^ r` followed by the first map
of `smoothGodementReductionSequence` is the projection `lim_m H^n(Φ(F_m^•)) ⟶ H^n(Φ(F_r^•))`. -/
@[reassoc (attr := simp)]
lemma reductionπ_smoothGodementReductionSequence_f :
    reductionπ ℓ (limit (smoothGodementSectionsTower h T Φ ⋙
        HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n)) r ≫
        (smoothGodementReductionSequence hS n hn hcmp).f =
      limit.π (smoothGodementSectionsTower h T Φ ⋙
        HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n) (op r) :=
  cokernel.π_desc _ _ _

/-- The second map of `smoothGodementReductionSequence` followed by the inclusion of the
`ℓ ^ r`-torsion is `smoothGodementReductionδ`. -/
@[reassoc (attr := simp)]
lemma smoothGodementReductionSequence_g_ι :
    (smoothGodementReductionSequence hS n hn hcmp).g ≫
        kernel.ι (powSMul ℓ r (limit (smoothGodementSectionsTower h T Φ ⋙
          HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) (n + 1)))) =
      smoothGodementReductionδ hS n hn :=
  kernel.lift_ι _ _ _

/-- `adicLevelReductionSequence` for the truncated smooth Godement section system is isomorphic
to `smoothGodementReductionSequence`, through `smoothGodementTruncatedSectionsAdicCohomologyIso`
and `smoothGodementTruncatedSectionsLevelHomologyIso`. -/
def adicLevelReductionSequenceSmoothGodementIso :
    adicLevelReductionSequence hS n hcmp ≅ smoothGodementReductionSequence hS n hn hcmp :=
  cokernelKernelShortComplexIso
    (smoothGodementTruncatedSectionsAdicCohomologyIso h T D Φ hterm hres (Nat.le_succ_of_le hn))
    (smoothGodementTruncatedSectionsAdicCohomologyIso h T D Φ hterm hres (Nat.le_succ_of_le hn))
    (smoothGodementTruncatedSectionsLevelHomologyIso h T D Φ hterm hres r (Nat.le_succ_of_le hn))
    (smoothGodementTruncatedSectionsAdicCohomologyIso h T D Φ hterm hres (Nat.succ_le_succ hn))
    (smoothGodementTruncatedSectionsAdicCohomologyIso h T D Φ hterm hres (Nat.succ_le_succ hn))
    (comp_powSMul ℓ r _).symm
    (π_smoothGodementTruncatedSectionsLevelHomologyIso_hom h T D Φ hterm hres r _)
    (smoothGodementReductionδ_comm hS n hn) (comp_powSMul ℓ r _).symm

/-- Milne, Ch. V, Lemma 1.11, for Harris's truncated smooth Godement section systems: for
`n ≤ D`, if `adicLimitComparison` of the truncated section system is an isomorphism in degrees
`n` and `n + 1`, then
`0 ⟶ (lim_m H^n(Φ(F_m^•))) / ℓ ^ r ⟶ H^n(Φ(F_r^•)) ⟶ (lim_m H^{n+1}(Φ(F_m^•)))[ℓ ^ r] ⟶ 0` is short
exact. -/
theorem smoothGodementReductionSequence_shortExact
    (hcmp' : IsIso
      ((smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).adicLimitComparison (n + 1))) :
    (smoothGodementReductionSequence hS n hn hcmp).ShortExact :=
  ShortComplex.shortExact_of_iso (adicLevelReductionSequenceSmoothGodementIso hS n hn hcmp)
    (adicLevelReductionSequence_shortExact hS n hcmp hcmp')

end SmoothGodement

section SmoothGodementModules

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ}
  (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)
  (D : ℕ)

/-- Milne, Ch. V, Lemma 1.11, for Harris's truncated smooth Godement section systems with values
in `R'`-modules: given `FiniteCohomologyInverseLimitStatement` and finite cohomology of the
truncated section complexes, for `n ≤ D`,
`0 ⟶ (lim_m H^n(Φ(F_m^•))) / ℓ ^ r ⟶ H^n(Φ(F_r^•)) ⟶ (lim_m H^{n+1}(Φ(F_m^•)))[ℓ ^ r] ⟶ 0` is short
exact. -/
theorem smoothGodementReductionSequence_shortExact_of_finite {R' : Type u'} [CommRing R']
    (Φ : SmoothTopologicalSheaf R G X ⥤ ModuleCat.{v'} R') [Φ.Additive]
    [PreservesFiniteLimits Φ]
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h T q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementResidualSystem h T (D + 1)).projection hm)))
    (hF : FiniteCohomologyInverseLimitStatement.{u', v'} R')
    (hfin : ∀ m n, Finite
      (((smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).obj m).homology n))
    (r n : ℕ) (hn : n ≤ D) :
    (smoothGodementReductionSequence
      (reductionShortComplex_shortExact_moduleCat
        (smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).extendSystem r) n hn
      (isIso_adicLimitComparison_of_finite hF _ hfin n)).ShortExact :=
  smoothGodementReductionSequence_shortExact _ _ _ _
    (isIso_adicLimitComparison_of_finite hF _ hfin _)

/-- The representation version of `smoothGodementReductionSequence_shortExact_of_finite`, for a
sections functor `Φ` with values in representations of a monoid `G'` over `k`. -/
theorem smoothGodementReductionSequence_shortExact_rep {k : Type u'} [CommRing k]
    {G' : Type w} [Monoid G'] (Φ : SmoothTopologicalSheaf R G X ⥤ Rep.{v'} k G') [Φ.Additive]
    [PreservesFiniteLimits Φ]
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h T q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementResidualSystem h T (D + 1)).projection hm)))
    (hF : FiniteCohomologyInverseLimitStatement.{u', v'} k)
    (hfin : ∀ m n, Finite
      (((smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).obj m).homology n))
    (r n : ℕ) (hn : n ≤ D) :
    (smoothGodementReductionSequence
      (reductionShortComplex_shortExact_rep
        (smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).extendSystem r) n hn
      (isIso_adicLimitComparison_rep hF _ hfin n)).ShortExact :=
  smoothGodementReductionSequence_shortExact _ _ _ _
    (isIso_adicLimitComparison_rep hF _ hfin _)

end SmoothGodementModules

end DivisibleSystem

end Langlands.Cohomology
