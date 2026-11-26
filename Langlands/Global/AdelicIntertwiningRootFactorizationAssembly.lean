import Langlands.Global.AdelicIntertwiningRootFactorizationReduction
import Langlands.Global.AdelicIntertwiningElementaryChainStatement
import Langlands.Global.AdelicIntertwiningCocycleStatement
import Langlands.Global.AdelicIntertwiningIdentity
import Langlands.Global.AdelicEisensteinRegularRegion
import Langlands.Global.AdelicWeylParameterEquivalence
import Langlands.Global.AdelicWeylSetAssociation
import Langlands.GroupScheme.Rational.ParabolicCharacterLattice
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.Analysis.Meromorphic.RootFactorizedExpansion

/-! # Root factorization of intertwining operators from continuation, cocycle and chain inputs

Bernstein–Lapid §8.6, number field case: `IntertwiningRootFactorizationStatement` follows from
the meromorphic continuation of intertwining operators
(`IntertwiningMeromorphicContinuationStatement`), their cocycle relation
(`IntertwiningCocycleStatement`), the passage to a standard parabolic family with a maximal
compact subgroup that has Iwasawa coverage for every standard parabolic
(`IntertwiningStandardizationStatement`) and the decomposition into elementary steps with
rank-one invariance (`IntertwiningElementaryChainStatement`). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

section Regular

variable {F : Type u} [Field F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}

/-- For every bound `R₀` and every translation `ν`, the parameters `λ` such that `λ` and
`λ + ν` are both `R₀`-regular contain the image of a nonempty open set of a chart. -/
theorem exists_isOpen_regular_and_translate (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    [FiniteDimensional ℂ (ComplexCharacterParameter F P)] (R₀ : ℝ)
    (ν : ComplexCharacterParameter F P) :
    ∃ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) (O : Set (Fin n → ℂ)),
      IsOpen O ∧ O.Nonempty ∧ ∀ s ∈ O, r.IsRegularParameter hA hT R₀ (e s) ∧
        r.IsRegularParameter hA hT R₀ (e s + ν) := by
  classical
  let e := (Module.finBasis ℂ (ComplexCharacterParameter F P)).equivFun.symm
  let B := Langlands.Plancherel.weylInducedCharacterForm hA hT r.data.f r.data.i
  let Lf : characterLattice A → ComplexCharacterParameter F P → ℝ := fun α x =>
    B (realParameterRestriction (a ≫ l) (parameterRealPart F P x)) ((1 : ℝ) ⊗ₜ[ℤ] α)
  have hadd : ∀ α x y, Lf α (x + y) = Lf α x + Lf α y := by
    intro α x y
    simp only [Lf, map_add, LinearMap.add_apply]
  have hfin : r.unipotentRoots.Finite :=
    ((hT.finite_positiveRelativeRoots r.data.i r.data.ν).image
      (fun χ => r.data.f ≫ χ)).subset (by
        rintro α ⟨-, χ, hχ, rfl⟩
        exact ⟨χ, hχ, rfl⟩)
  let c : ℝ := ∑ α ∈ hfin.toFinset, |Lf α ν|
  have hc : 0 ≤ c := Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨lam, hlam⟩ := r.exists_regularParameter hA hT (R₀ + c)
  have hopen := r.isOpen_regularParameter_inCoordinates hA hT R₀ e
  refine ⟨_, e, {s | r.IsRegularParameter hA hT R₀ (e s)} ∩
    {s | r.IsRegularParameter hA hT R₀ (e s + ν)}, ?_, ⟨e.symm lam, ?_, ?_⟩, fun s hs => hs⟩
  · refine hopen.inter ?_
    have heq : {s | r.IsRegularParameter hA hT R₀ (e s + ν)} =
        (fun s => s + e.symm ν) ⁻¹' {s | r.IsRegularParameter hA hT R₀ (e s)} := by
      ext s
      simp [map_add]
    rw [heq]
    exact hopen.preimage (continuous_id.add continuous_const)
  · intro α hα
    have h1 : R₀ + c < Lf α lam := hlam α hα
    show R₀ < Lf α (e (e.symm lam))
    rw [LinearEquiv.apply_symm_apply]
    linarith
  · intro α hα
    have h1 : R₀ + c < Lf α lam := hlam α hα
    have hle : |Lf α ν| ≤ c :=
      Finset.single_le_sum (f := fun α => |Lf α ν|) (fun _ _ => abs_nonneg _)
        (hfin.mem_toFinset.2 hα)
    have h2 := neg_abs_le (Lf α ν)
    show R₀ < Lf α (e (e.symm lam) + ν)
    rw [LinearEquiv.apply_symm_apply, hadd]
    linarith

end Regular


/-- The inputs of the root factorization: meromorphic continuation, cocycle relation,
standardization and elementary decomposition of intertwining operators. -/
def IntertwiningRootFactorizationAssemblyStatement : Prop :=
  IntertwiningMeromorphicContinuationStatement.{u} → IntertwiningCocycleStatement.{u} →
    IntertwiningStandardizationStatement.{u} → IntertwiningElementaryChainStatement.{u} →
      IntertwiningRootFactorizationStatement.{u}

/-- **Root factorization of continued intertwining operators from its inputs** (Bernstein–Lapid
§8.6). Pass to a standard family with a maximal compact subgroup that has Iwasawa coverage for
every standard parabolic, decompose the standard Weyl element into elementary steps, and
compose the continued expansions of the steps by the cocycle relation; the coefficients of each
step are invariant under the kernel of one root form, which pulls back to the kernel of a root
form of `P`. -/
theorem intertwiningRootFactorization_of_inputs :
    IntertwiningRootFactorizationAssemblyStatement.{u} := by
  intro hIC hCO hST hEC F _ _ G P M U Q M' V A _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT q _ iV l' _ π'
    w c hG hU hq hV hl' hmul hπ hw K hK hK' N d rho hsmooth hcalc φ hKmax hrho hφ
  obtain ⟨fam, I, I', K₀, hK₀, w₀, c₀, π₀, iota, m, E, h, τ, φ₀, hK₀max, hw₀, hπ₀, hφ₀, hE,
    instW, instP, instF, hregι, hrootι, R₁, hcomp⟩ :=
    hST F G P M U Q M' V A p iU l a r hA hT q iV l' π' w c hG hU hq hV hl' hmul hπ hw K hK hK'
      rho hsmooth hcalc φ hKmax hrho hφ
  let : Fintype (relativeWeylGroup fam.i) := instW
  have : ∀ J₀, IsClosedImmersion (fam.p J₀).hom.hom.left := instP
  have : ∀ J₀, Mono (CommGroupScheme.groupHom (fam.f J₀)).hom.hom.left := instF
  obtain ⟨n, J, ws, cs, W, C, πs, hW0, hC0, hrec, hπs, hmuls, hws, hsteps, Rid, hid⟩ :=
    hEC F G fam K₀ hK₀ I I' w₀ c₀ π₀ hK₀max hw₀ hπ₀
  -- finite dimensionality of the parameter spaces
  have hfdP : FiniteDimensional ℂ (ComplexCharacterParameter F P) := by
    have := (r.rationalCharacters_free_finite hG).2
    exact Module.Finite.base_change ℤ ℂ _
  have hfdJ : ∀ J₀ : StandardIndex F G fam.i fam.ν,
      FiniteDimensional ℂ (ComplexCharacterParameter F (fam.P J₀)) := fun J₀ => by
    have := ((fam.rootPresentation J₀).rationalCharacters_free_finite hG).2
    exact Module.Finite.base_change ℤ ℂ _
  -- the partial composites present elements of `W(P_I, P_{J' t})`
  have hWC : ∀ t : Fin (n + 1), IsWeylConjugation (fam.p I) (fam.l I)
      (fam.p ((Fin.cons I J : Fin (n + 1) → StandardIndex F G fam.i fam.ν) t))
      (fam.l ((Fin.cons I J : Fin (n + 1) → StandardIndex F G fam.i fam.ν) t)) (W t) (C t) := by
    intro t
    induction t using Fin.induction with
    | zero =>
      rw [hW0, hC0]
      have hone : ∀ {X Y : GroupScheme (Spec (CommRingCat.of F))} (p₀ : Y ⟶ G) (l₀ : X ⟶ Y),
          IsWeylConjugation p₀ l₀ p₀ l₀ 1 (𝟙 X) := fun p₀ l₀ => by
        refine ⟨inferInstance, ?_⟩
        have h1 : (G.innerIso 1).inv = 𝟙 G := by
          rw [← cancel_epi (G.innerIso 1).hom, Iso.hom_inv_id, innerIso_one_hom,
            Category.comp_id]
        rw [h1, Category.id_comp, Category.comp_id]
      exact hone (fam.p I) (fam.l I)
    | succ t ih =>
      rw [(hrec t).1, (hrec t).2]
      exact ih.comp (hws t)
  -- induction along the chain
  have key : ∀ t : Fin (n + 1), ∀ ψ : AdelicGroupPoints F G → ℂ,
      IsAutomorphicFunctionOn F G hsmooth hcalc
          (parabolicQuotientSubgroup F (fam.p I) (fam.iU I) (fam.l I))
          (K₀.comap (ofInfinite F G).toMonoidHom) rho ψ →
      HasRootFactorizedExpansion
        ((fam.rootPresentation I).rootFunctional
          (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
          fam.maximalSplit.isSplitSubtorus.1)
        (fam.rootPresentation I).unipotentRoots
        (fun R₀ mu => (fam.rootPresentation I).IsRegularParameter
          (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
          fam.maximalSplit.isSplitSubtorus.1 R₀ mu)
        (IsAutomorphicFunctionOn F G hsmooth hcalc
          (parabolicQuotientSubgroup F
            (fam.p ((Fin.cons I J : Fin (n + 1) → StandardIndex F G fam.i fam.ν) t))
            (fam.iU ((Fin.cons I J : Fin (n + 1) → StandardIndex F G fam.i fam.ν) t))
            (fam.l ((Fin.cons I J : Fin (n + 1) → StandardIndex F G fam.i fam.ν) t)))
          (K₀.comap (ofInfinite F G).toMonoidHom) rho)
        (fun mu g => (hK₀ I).intertwiningOperator (hK₀ _) (fam.iU I) (fam.l I) (fam.iU _)
          (C t) (πs t) (W t) ψ mu g) := by
    intro t
    induction t using Fin.induction with
    | zero =>
      intro ψ hψ
      have hinvU : IsLeftInvariantUnder F G (parabolicUnipotentImage F (fam.p I) (fam.iU I)) ψ :=
        fun x hx g => hψ.1 x (Subgroup.mem_sup_left hx) g
      refine hasRootFactorizedExpansion_of_eq hψ fun mu g => ?_
      rw [hW0, hC0]
      exact (hK₀ I).intertwiningOperator_one_self (fam.iU I) (fam.rootPresentation I) (πs 0)
        (hπs 0) (fam.isUnipotentRadical I) ψ hinvU mu g
    | succ t ih =>
      intro ψ hψ
      have hWCt := hWC t.castSucc
      have := hWCt.isIso
      obtain ⟨We, hWe⟩ := exists_weylParameter_linearEquiv (F := F) (fam.l I)
        (fam.l ((Fin.cons I J : Fin (n + 1) → StandardIndex F G fam.i fam.ν) t.castSucc))
        (fam.isCompatible I).levi (fam.isCompatible _).levi (C t.castSucc) (πs t.castSucc)
        (hπs t.castSucc)
      have hWe' : ∀ x, We x = weylParameter (fam.l I) (C t.castSucc) (πs t.castSucc) x :=
        fun x => LinearMap.congr_fun hWe x
      obtain ⟨α, -, ⟨Rinv, hinvS⟩, β, hβ, hβα⟩ := hsteps t
      refine HasRootFactorizedExpansion.step We
        ((fam.rootPresentation _).rootFunctional
          (fam.isCompatible _).splitComponent.isCentralSplitTorus.1.1
          fam.maximalSplit.isSplitSubtorus.1 α)
        (RegY := fun R₀ mu => (fam.rootPresentation
          ((Fin.cons I J : Fin (n + 1) → StandardIndex F G fam.i fam.ν) t.castSucc)).IsRegularParameter
          (fam.isCompatible _).splitComponent.isCentralSplitTorus.1.1
          fam.maximalSplit.isSplitSubtorus.1 R₀ mu)
        (S := fun mu χ g => (hK₀ _).intertwiningOperator (hK₀ _) (fam.iU _) (fam.l _)
          (fam.iU _) (cs t) (πs t.succ) (ws t) χ mu g)
        (fun hle h α hα => hle.trans_lt (h α hα))
        (fun R₀ ν => exists_isOpen_regular_and_translate _ _ _ R₀ ν)
        ⟨β, hβ, fun ν hν => by rw [hWe']; exact hβα ν hν⟩ (ih ψ hψ)
        (fun χ hχ => hIC F G _ _ _ _ _ _ _ (fam.p _) (fam.iU _) (fam.l _) (fam.a _)
          (fam.rootPresentation _) _ _ (fam.p _) (fam.iU _) (fam.l _) (πs t.succ) (ws t) (cs t)
          hG (fam.isUnipotentRadical _) (fam.isCompatible _).parabolic
          (fam.isUnipotentRadical _) (fam.isCompatible _).levi (hmuls t.succ) (hπs t.succ)
          (hws t) K₀ (hK₀ _) (hK₀ _) rho hsmooth hcalc χ hK₀max hrho hχ)
        (fun χ _ => ⟨Rinv, fun mu nu h1 h2 h3 g => hinvS mu nu h1 h2 h3 χ g⟩)
        (hIC F G _ _ _ _ _ _ _ (fam.p I) (fam.iU I) (fam.l I) (fam.a I)
          (fam.rootPresentation I) _ _ (fam.p _) (fam.iU _) (fam.l _) (πs t.succ) (W t.succ)
          (C t.succ) hG (fam.isUnipotentRadical I) (fam.isCompatible _).parabolic
          (fam.isUnipotentRadical _) (fam.isCompatible _).levi (hmuls t.succ) (hπs t.succ)
          (hWC t.succ) K₀ (hK₀ _) (hK₀ _) rho hsmooth hcalc ψ hK₀max hrho hψ) ?_
      intro k χ a D hχ ha hag₀ k' ξ b D' hb hagS k'' ζ cc D'' hc hag₁ x hx hxD' g
      have hag₁' := hag₁
      simp only [(hrec t).1, (hrec t).2] at hag₁'
      have hrel := hCO F G _ _ _ _ _ _ _ _ _ _ _ (fam.p I) (fam.iU I) (fam.l I) (fam.a I)
        (fam.rootPresentation I) _ _ (fam.p _) (fam.iU _) (fam.l _) (fam.a _)
        (fam.rootPresentation _) _ _ (πs t.castSucc) (fam.p _) (fam.iU _) (fam.l _) (πs t.succ)
        (W t.castSucc) (ws t) (C t.castSucc) (cs t) hG (fam.isUnipotentRadical I)
        (fam.isUnipotentRadical _) (fam.isCompatible _).parabolic (fam.isUnipotentRadical _)
        (fam.isCompatible _).levi (hmuls t.succ) (hπs t.castSucc) (hπs t.succ) hWCt (hws t) K₀
        (hK₀ _) (hK₀ _) (hK₀ _) rho hsmooth hcalc ψ hK₀max hrho hψ k χ a D hχ ha hag₀ k' ξ b D'
        hb hagS k'' ζ cc D'' hc hag₁' x hx (by rw [← hWe']; exact hxD') g
      rw [hWe']
      exact hrel
  -- the comparison with the composite of the chain
  obtain ⟨Rι, hRι⟩ := hregι Rid
  have hTcomp : ∃ R' : ℝ, ∀ lam, r.IsRegularParameter hA hT R' lam → ∀ g,
      hK.intertwiningOperator hK' iU l iV c π' w φ lam g =
        ∑ j, E j lam * h j g *
          (fun (j : Fin m) mu g => (hK₀ I).intertwiningOperator (hK₀ _) (fam.iU I) (fam.l I)
            (fam.iU _) (C (Fin.last n)) (πs (Fin.last n)) (W (Fin.last n)) (φ₀ j) mu g) j
            (iota lam) (τ j g) := by
    refine ⟨max R₁ Rι, fun lam hlam g => ?_⟩
    rw [hcomp lam (fun α hα => (le_max_left _ _).trans_lt (hlam α hα)) g]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hid (iota lam) (hRι lam fun α hα => (le_max_right _ _).trans_lt (hlam α hα)) (φ₀ j)
      (hφ₀ j).1 (τ j g)]
  obtain ⟨k, ψ, coeff, D, hmer, hag, Jn, nn, fac, hfac, heq⟩ :=
    exists_rootFactorization_of_combination (L := r.rootFunctional hA hT) (R := r.unipotentRoots)
      (RegX := fun R₀ lam => r.IsRegularParameter hA hT R₀ lam)
      (fun hle h α hα => hle.trans_lt (h α hα)) iota hregι hrootι E hE h τ _
      (fun j => key (Fin.last n) (φ₀ j) (hφ₀ j)) _ hTcomp
  exact ⟨k, ψ, coeff, D, hmer, hag, Jn, nn, fac, hfac, heq⟩

end Langlands.Global
