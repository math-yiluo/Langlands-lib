import Langlands.GroupScheme.Rational.FullParabolicLevi
import Langlands.GroupScheme.Rational.MaximalLeviCentralKernel
import Langlands.GroupScheme.Rational.RelativeRankOneParabolicMaximality
import Langlands.Representation.CuspidalSupport.InducedProgeneratorIndependenceReduction
import Langlands.Representation.CuspidalSupport.InducedProgeneratorInertialNormalizer
import Langlands.Representation.CuspidalSupport.InducedProgeneratorMixedJacquet
import Langlands.Representation.Exponents.LeviInductionDualityAdjunction
import Langlands.Representation.Exponents.MaximalLeviBlockStatements
import Langlands.Representation.Exponents.RepresentedSupercuspidalityTransport
import Langlands.Representation.Filtration.SubquotientAlgebraProof
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # The induced progenerator comparison for opposite maximal parabolics -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme CuspidalSupport Plancherel

/-- The maximal-Levi block theorem implies independence of the induced
progenerator for conjugate Levi embeddings. -/
def InducedProgeneratorIndependenceFromMaximalLeviBlockStatement : Prop :=
  MaximalLeviBlockStatements.{u, v} → InducedProgeneratorIndependenceStatement.{u, v}

section Maximality

variable {k : Type u} [Field k]
  {G P M Q : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

private theorem maximal_of_commonLevi
    (hG : IsConnectedReductive G)
    {p : P ⟶ G} {l : M ⟶ P} {q : Q ⟶ G} {lQ : M ⟶ Q}
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
    (hlevi : lQ ≫ q = l ≫ p) (hproper : ¬ IsIso p)
    (hmax : ∀ (R : GroupScheme (Spec (CommRingCat.of k))) (t : R ⟶ G) (f : P ⟶ R),
      IsParabolicSubgroup t → f ≫ t = p → IsIso f ∨ IsIso t) :
    (¬ IsIso q) ∧
    ∀ (R : GroupScheme (Spec (CommRingCat.of k))) (t : R ⟶ G) (f : Q ⟶ R),
      IsParabolicSubgroup t → f ≫ t = q → IsIso f ∨ IsIso t := by
  have hproperQ : ¬ IsIso q := by
    intro h
    let := h
    let := hlQ.isIso_of_isIso_parabolic (p := q) hG
    have : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
    apply hproper (isIso_of_full_range p (Over.mono_of_mono_left _) ?_)
    apply le_antisymm
    · exact SubgroupFunctor.le_def.mpr fun _ => le_top
    · rw [← full_range_of_isIso (lQ ≫ q), hlevi]
      exact SubgroupFunctor.range_comp_le l p
  let : Smooth G.X.hom := hG.smooth
  let : LocallyOfFiniteType G.X.hom := inferInstance
  obtain ⟨A, a, ha⟩ := (splitComponentStatement k M hl.isConnectedReductive).1
  let i := a ≫ l ≫ p
  obtain ⟨α₀, hα₀⟩ := hasCentralKernelCharacter_of_maximal parabolicDynamic hG hp hl hproper hmax ha
  have hzero (β : characterLattice A) (hβ : β ∈ relativeRoots i)
      (ν : cocharacterLattice A) (hν : latticePairing A α₀ ν = 0) :
      latticePairing A β ν = 0 := by
    have hcomp := root_restrict_eq_zero_of_isCentral i ν isSplitTorus_gm (hα₀ ν hν) hβ
    rw [latticePairing_apply, hcomp, AddEquiv.map_zero]
  have hrank : HasProportionalRootPairings i := by
    intro α hα β hβ ν eta
    by_cases hall : ∀ eta, latticePairing A α₀ eta = 0
    · rw [hzero α hα ν (hall ν), hzero β hβ ν (hall ν), zero_mul, zero_mul]
    · obtain ⟨mu, hmu⟩ := not_forall.mp hall
      have hcross (γ : characterLattice A) (hγ : γ ∈ relativeRoots i) (ω : cocharacterLattice A) :
          latticePairing A α₀ mu * latticePairing A γ ω =
            latticePairing A α₀ ω * latticePairing A γ mu := by
        let δ := latticePairing A α₀ mu • ω - latticePairing A α₀ ω • mu
        have hδ : latticePairing A α₀ δ = 0 := by
          simp only [δ, map_sub, map_zsmul, zsmul_eq_mul, Int.cast_id]
          ring
        have h := hzero γ hγ δ hδ
        simp only [δ, map_sub, map_zsmul, zsmul_eq_mul, Int.cast_id, sub_eq_zero] at h
        exact h
      apply mul_left_cancel₀ (mul_ne_zero hmu hmu)
      calc
        _ = (latticePairing A α₀ mu * latticePairing A α ν) *
            (latticePairing A α₀ mu * latticePairing A β eta) := by ring
        _ = (latticePairing A α₀ ν * latticePairing A α mu) *
            (latticePairing A α₀ eta * latticePairing A β mu) :=
          congrArg₂ (· * ·) (hcross α hα ν) (hcross β hβ eta)
        _ = (latticePairing A α₀ ν * latticePairing A β mu) *
            (latticePairing A α₀ eta * latticePairing A α mu) := by ring
        _ = (latticePairing A α₀ mu * latticePairing A β ν) *
            (latticePairing A α₀ mu * latticePairing A α eta) :=
          congrArg₂ (· * ·) (hcross β hβ ν).symm (hcross α hα eta).symm
        _ = _ := by ring
  exact ⟨hproperQ, isMaximalParabolic_of_proportional_splitComponent_pairings
    hG hq hlQ ha hproperQ (by simpa only [i, hlevi] using hrank)⟩

end Maximality

open scoped CategoryTheory.MonObj

section Twisting

open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {M : GroupScheme (Spec (CommRingCat.of k))} [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]

local instance maximalOppositeLeviTopology : TopologicalSpace (rationalPoints M) :=
  rationalPointTopology k M.X
local instance maximalOppositeLeviTopologicalGroup : IsTopologicalGroup (rationalPoints M) :=
  rationalPoint_isTopologicalGroup k M

private theorem inertiaRelated_iff_twistIntertwiner
    (ρ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    IsRationalInertiaRelated M ρ σ ↔
      ∃ ψ : unramifiedCharacters
          (fun χ : rationalCharacters M => (rationalNormCharacters M χ).toMul),
        ∃ T : ρ ≃ₗ[ℂ] σ, ∀ (m : rationalPoints M) (x : ρ),
          (((ψ : rationalPoints M →ₜ* ℂˣ) m : ℂˣ) : ℂ) • T (ρ.representation m x) =
            σ.representation m (T x) := by
  constructor
  · rintro ⟨ψ, ⟨e⟩⟩
    let E := SmoothRep.equivOfIso e.symm
    refine ⟨ψ, E.toLinearEquiv, fun m x => ?_⟩
    have h := E.toIntertwiningMap.isIntertwining _ _ m x
    change E.toLinearEquiv ((((ψ : rationalPoints M →ₜ* ℂˣ) m : ℂˣ) : ℂ) •
      ρ.representation m x) = σ.representation m (E.toLinearEquiv x) at h
    simpa only [map_smul] using h
  · rintro ⟨ψ, T, hT⟩
    let e : rationalUnramifiedTwist M ψ ρ ≅ σ :=
      SmoothRep.mkIso (Representation.Equiv.mk T fun m => LinearMap.ext fun x => by
        change T ((((ψ : rationalPoints M →ₜ* ℂˣ) m : ℂˣ) : ℂ) • ρ.representation m x) =
          σ.representation m (T x)
        rw [map_smul]
        exact hT m x)
    exact ⟨ψ, ⟨e.symm⟩⟩

end Twisting

open Langlands.AlgebraicGeometry.PointTopology

set_option maxHeartbeats 2000000 in
/-- The maximal-Levi block equivalence gives the common-Levi comparison in the
case of disjoint inertia, while an inertial normalizer gives the comparison
by conjugation. -/
theorem inducedProgeneratorMaximalOpposite_of_maximalLeviBlockStatements
    (hBlock : MaximalLeviBlockStatements.{u, v}) :
    InducedProgeneratorMaximalOppositeStatement.{u, v} := by
  classical
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ _ _ P M N Q U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hlevi hinf hproper hmax
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have : Smooth M.X.hom := hl.isConnectedReductive.smooth
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  have : IsTopologicalGroup (rationalPoints M) := rationalPoint_isTopologicalGroup k M
  intro π hπ hsc ρ₀ hρ₀ j hj
  let A := rationalNormKernelSummandInduction M ρ₀
  let iP := leviInductionFunctor.{u, max u v} p l r hp hr hl hmul
  let iQ := leviInductionFunctor.{u, max u v} q lQ rQ hq hrQ hlQ hmulQ
  change Nonempty (iP.obj A ≅ iQ.obj A)
  by_cases heq : SubgroupFunctor.range p = SubgroupFunctor.range q
  · exact ⟨leviInductionIsoOfRangeEq p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
      heq.symm hlevi A⟩
  let ρ := rationalInertiaBaseLift M π
  let e : π.representation.Equiv ρ.representation := SmoothRep.universeLiftEquiv.{u} π
  let IsInertialNormalizer : (M ⟶ G) → Prop := fun i =>
    ∃ (g : rationalPoints G) (φ : M ≅ M),
      φ.hom ≫ i = i ≫ (G.innerIso g).hom ∧ g ∉ pointImage i ∧
        ∃ ψ : unramifiedCharacters
            (fun χ : rationalCharacters M => (rationalNormCharacters M χ).toMul),
          ∃ T : ρ ≃ₗ[ℂ] ρ, ∀ (m : rationalPoints M) (x : ρ),
            T (ρ.representation m x) =
              (((ψ : rationalPoints M →ₜ* ℂˣ) (rationalPoints.map φ.hom m) : ℂˣ) : ℂ) •
                ρ.representation (rationalPoints.map φ.hom m) (T x)
  by_cases hnorm : IsInertialNormalizer (l ≫ p)
  · obtain ⟨g, φ, hφ, hg, ψ, T, hT⟩ := hnorm
    let S := e.toLinearEquiv.trans (T.trans e.toLinearEquiv.symm)
    refine ⟨inducedProgeneratorIso_of_inertialNormalizer hG p l r hp hl hr hmul
      q lQ rQ hq hlQ hrQ hmulQ hlevi hinf hproper hmax heq g φ
      (by simpa only [Category.assoc] using hφ) hg π hπ ρ₀ hρ₀ j hj ψ S fun m x => ?_⟩
    apply e.toLinearEquiv.injective
    have he (m : rationalPoints M) (x : π) :
        e.toLinearEquiv (π.representation m x) = ρ.representation m (e.toLinearEquiv x) :=
      e.toIntertwiningMap.isIntertwining _ _ m x
    have hS (y : π) : e.toLinearEquiv (S y) = T (e.toLinearEquiv y) :=
      e.toLinearEquiv.apply_symm_apply _
    rw [map_smul, hS, he m x, he _ (S x), hS]
    exact hT m (e.toLinearEquiv x)
  obtain ⟨hproperQ, hmaxQ⟩ := maximal_of_commonLevi hG hp hl hq hlQ hlevi hproper hmax
  have hnormQ : ¬ IsInertialNormalizer (lQ ≫ q) := by
    rwa [hlevi]
  have hno (g : rationalPoints G) (φ : M ≅ M)
      (hφ : φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom)
      (hg : g ∉ pointImage (l ≫ p)) :
      ¬ IsRationalInertiaRelated M ρ
        (rationalInertiaBaseLift M (SmoothRep.pullback (ambientIsoPointsEquiv φ) π)) := by
    rintro ⟨ψ, ⟨E⟩⟩
    let T : ρ ≃ₗ[ℂ] ρ := (SmoothRep.equivOfIso E).toLinearEquiv
    have hφ' : (l ≫ p) ≫ (G.innerIso g).hom = φ.hom ≫ (l ≫ p) := hφ.symm
    refine hnorm ⟨g⁻¹, φ.symm, (comp_innerIso_inv_hom hφ').symm, fun h =>
      hg ((pointImage (l ≫ p)).inv_mem_iff.mp h), ψ, T, fun m x => ?_⟩
    have hm : rationalPoints.map φ.hom (rationalPoints.map φ.inv m) = m :=
      (ambientIsoPointsEquiv φ).apply_symm_apply m
    have h := (SmoothRep.equivOfIso E).toIntertwiningMap.isIntertwining _ _
      (rationalPoints.map φ.inv m) x
    change T (ρ.representation (rationalPoints.map φ.hom (rationalPoints.map φ.inv m)) x) =
      (((ψ : rationalPoints M →ₜ* ℂˣ) (rationalPoints.map φ.inv m) : ℂˣ) : ℂ) •
        ρ.representation (rationalPoints.map φ.inv m) (T x) at h
    rwa [hm] at h
  have hnoQ (g : rationalPoints G) (φ : M ≅ M)
      (hφ : φ.hom ≫ lQ ≫ q = lQ ≫ q ≫ (G.innerIso g).hom)
      (hg : g ∉ pointImage (lQ ≫ q)) :
      ¬ IsRationalInertiaRelated M ρ
        (rationalInertiaBaseLift M (SmoothRep.pullback (ambientIsoPointsEquiv φ) π)) :=
    hno g φ (by simpa only [← Category.assoc lQ q, hlevi, Category.assoc] using hφ)
      (by simpa only [hlevi] using hg)
  have hρ : ρ.IsIrreducible := (SmoothRep.isIrreducible_universeLift_iff π).mpr hπ
  have hscρ : IsSupercuspidal ρ := by
    intro R L V t a b ht ha hb hmul' htproper
    apply (jacquet_subsingleton_iff_coinvariants t a b ht ha hb hmul' ρ).mpr
    have hzero := (jacquet_subsingleton_iff_coinvariants t a b ht ha hb hmul' π).mp
      (hsc R L V t a b ht ha hb hmul' htproper)
    let equiv := Jacquet.Localization.representationEquiv (pointImage (b ≫ t)) 1 e
    have : Subsingleton (Jacquet.Localization.Coinvariants π.representation
        (pointImage (b ≫ t)) 1) := by
      simpa only [Jacquet.Localization.Coinvariants, Jacquet.Localization.relations_one,
        Jacquet.Coinvariants, Representation.Coinvariants] using hzero
    have hLift := equiv.symm.injective.subsingleton
    simpa only [Jacquet.Localization.Coinvariants, Jacquet.Localization.relations_one,
      Jacquet.Coinvariants, Jacquet.relations, Representation.Coinvariants] using hLift
  obtain ⟨irredP, -, intoP, -, -, -⟩ :=
    hBlock k G hG P M N p l r hp hl hr hmul hproper hmax ρ hρ hscρ hnorm
  obtain ⟨-, -, intoQ, fullQ, faithfulQ, ontoQ⟩ :=
    hBlock k G hG Q M U q lQ rQ hq hlQ hrQ hmulQ hproperQ hmaxQ ρ hρ hscρ hnormQ
  let IsTwist (σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M)) :=
    ∃ ψ : unramifiedCharacters
        (fun χ : rationalCharacters M => (rationalNormCharacters M χ).toMul),
      ∃ T : ρ ≃ₗ[ℂ] σ, ∀ (m : rationalPoints M) (x : ρ),
        (((ψ : rationalPoints M →ₜ* ℂˣ) m : ℂˣ) : ℂ) • T (ρ.representation m x) =
          σ.representation m (T x)
  let InBlockM : ObjectProperty (SmoothRep.{0, u, max u v} ℂ (rationalPoints M)) :=
    fun X => ∀ σ, σ.IsIrreducible → SmoothRep.IsSubquotient σ X → IsTwist σ
  have hA : rationalInertiaBlockProperty M ρ A :=
    rationalSummandInduction_mem_block M hl.isConnectedReductive π hπ ρ₀ hρ₀ j hj
  have memA : InBlockM A := fun σ hσ hsub =>
    (inertiaRelated_iff_twistIntertwiner ρ σ).mp (hA σ hσ hsub)
  let rP := leviJacquetFunctor.{u, max u v} p l r hp hr hl hmul
  let rQ' := leviJacquetFunctor.{u, max u v} q lQ rQ hq hrQ hlQ hmulQ
  let adjP : rP ⊣ iP := leviFirstAdjointnessAdjunction p l r hp hl hr hmul
  let adjQ : rQ' ⊣ iQ := leviFirstAdjointnessAdjunction q lQ rQ hq hlQ hrQ hmulQ
  have hinfQ : SubgroupFunctor.range q ⊓ SubgroupFunctor.range p = SubgroupFunctor.range (lQ ≫ q) := by
    rw [hlevi, ← hinf]
    apply SubgroupFunctor.ext
    intro T
    simp only [SubgroupFunctor.inf_carrier, inf_comm]
  let projP := mixedJacquetInertialProjection hG q lQ rQ hq hlQ hrQ hmulQ
    p l r hp hl hr hmul hlevi.symm hinfQ hproperQ hmaxQ (Ne.symm heq)
    π hπ hsc ρ₀ hρ₀ j hj hnoQ
  let projQ := mixedJacquetInertialProjection hG p l r hp hl hr hmul
    q lQ rQ hq hlQ hrQ hmulQ hlevi hinf hproper hmax heq π hπ hsc ρ₀ hρ₀ j hj hno
  obtain ⟨X, hX, ⟨isoX⟩⟩ := ontoQ (iP.obj A) (by
    intro τ hτ hτsub
    obtain ⟨σ, hσ, hσsub⟩ := intoP A memA τ hτ hτsub
    obtain ⟨b, hb⟩ := exists_nonzero_rationalNormKernelSummandInduction M π ρ₀ j hρ₀ hj σ
      ((inertiaRelated_iff_twistIntertwiner ρ σ).mpr hσ)
    let a : rP.obj (iQ.obj A) ⟶ A := projP.1
    have hab : a ≫ b ≠ 0 := by
      intro h
      apply hb
      have hh := congrArg (fun z => projP.2.val ≫ z) h
      simpa only [a, ← Category.assoc, projP.2.property.1, Category.id_comp, Limits.comp_zero]
        using hh
    let f := adjP.homEquiv (iQ.obj A) σ (a ≫ b)
    have : rP.Additive := by
      let := leviInductionFunctor_additive.{u, max u v} p l r hp hr hl hmul
      exact adjP.left_adjoint_additive
    have hf : f ≠ 0 := fun h => hab ((adjP.homEquiv (iQ.obj A) σ).injective
      (h.trans (adjP.homAddEquiv_zero _ _).symm))
    have hf' : SmoothRep.hom f ≠ 0 := fun h => hf (by rw [← SmoothRep.ofHom_hom f, h]; rfl)
    have : (iP.obj σ).representation.IsIrreducible := irredP σ hσ
    have hquot : SmoothRep.IsQuotient (iP.obj σ) (iQ.obj A) :=
      ⟨f, (Representation.IsIrreducible.surjective_or_eq_zero _).resolve_right hf'⟩
    exact intoQ A memA τ hτ
      (smoothSubquotientTransitivity ℂ _ _ _ _ hσsub hquot.isSubquotient))
  let f : iP.obj A ⟶ iQ.obj A := adjQ.homEquiv (iP.obj A) A projQ.1
  let F := InBlockM.ι ⋙ iQ
  have : F.Full := fullQ
  have : F.Faithful := faithfulQ
  let A' : InBlockM.FullSubcategory := ⟨A, memA⟩
  have hcomp (Z : InBlockM.FullSubcategory) :
      Function.Bijective (fun g : iQ.obj A ⟶ iQ.obj Z.obj => f ≫ g) := by
    have hmem : rationalInertiaBlockProperty M ρ Z.obj := fun σ hσ hsub =>
      (inertiaRelated_iff_twistIntertwiner ρ σ).mpr (Z.property σ hσ hsub)
    have hmap : Function.Bijective (fun t : A ⟶ Z.obj => iQ.map t) := by
      constructor
      · intro s t h
        have h' : F.map (ObjectProperty.homMk (X := A') (Y := Z) s) =
            F.map (ObjectProperty.homMk (X := A') (Y := Z) t) := h
        exact congrArg (fun (a : A' ⟶ Z) => a.hom) (F.map_injective h')
      · intro g
        obtain ⟨t, ht⟩ := F.map_surjective (X := A') (Y := Z) g
        exact ⟨t.hom, ht⟩
    have hnat (t : A ⟶ Z.obj) :
        f ≫ iQ.map t = adjQ.homEquiv (iP.obj A) Z.obj (projQ.1 ≫ t) :=
      (adjQ.homEquiv_naturality_right projQ.1 t).symm
    apply (Function.Bijective.of_comp_iff _ hmap).mp
    simpa only [Function.comp_def, hnat] using
      (adjQ.homEquiv (iP.obj A) Z.obj).bijective.comp (projQ.2.property.2 Z.obj hmem)
  obtain ⟨t, ht⟩ := (hcomp ⟨X, hX⟩).surjective isoX.inv
  change f ≫ t = isoX.inv at ht
  let g : iQ.obj A ⟶ iP.obj A := t ≫ isoX.hom
  have hfg : f ≫ g = 𝟙 (iP.obj A) := by
    rw [show g = t ≫ isoX.hom from rfl, ← Category.assoc, ht, Iso.inv_hom_id]
  have hgf : g ≫ f = 𝟙 (iQ.obj A) :=
    (hcomp A').injective (by rw [← Category.assoc, hfg, Category.id_comp, Category.comp_id])
  exact ⟨⟨f, g, hfg, hgf⟩⟩

/-- Transport the opposite maximal comparison through a common-Levi gallery. -/
theorem inducedProgeneratorIndependence_of_maximalLeviBlockStatements :
    InducedProgeneratorIndependenceFromMaximalLeviBlockStatement.{u, v} :=
  fun hBlock => inducedProgeneratorIndependence_of_maximalOpposite
    (inducedProgeneratorMaximalOpposite_of_maximalLeviBlockStatements hBlock)

end Langlands.Aubert.General.RepresentedParabolic
