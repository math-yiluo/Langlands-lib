import Langlands.Representation.Aubert.General.SameLeviPieceDisplacementProof
import Langlands.Representation.Intertwining.PieceActionQuotientFiniteness
import Langlands.Representation.Intertwining.PQPredecessorFiltration
import Langlands.Representation.Intertwining.PQRegularityFiltration
import Langlands.Representation.Plancherel.UnramifiedMonomialSeparation
import Langlands.Representation.Exponents.UnramifiedJacquetExponentTwist
import Langlands.Representation.Exponents.GeometricLemmaSplitComponent
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityProof
import Langlands.Representation.Exponents.LeviJacquetFiniteTypeProof
import Langlands.Representation.Geometric.RepresentedGeometricLemmaProof
import Langlands.Representation.Smooth.IsotypicProjector
import Langlands.Representation.Smooth.Schur.Proof

/-! # Generic PQ-regularity of unramified twists for same-Levi parabolics -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme
open Langlands.PQFiniteActionRegularity

section Central

variable {k : Type u} [Field k]
  {M : GroupScheme (Spec (CommRingCat.of k))} {A : CommGroupScheme (Spec (CommRingCat.of k))}
  [TopologicalSpace (rationalPoints M)] [IsTopologicalGroup (rationalPoints M)]

/-- Schur's lemma for a split component: it acts on an irreducible admissible
representation through a character. -/
theorem exists_splitComponent_scalar {a : A.toGrp ⟶ M} (ha : IsSplitComponent a)
    (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)) (hirr : σ.IsIrreducible)
    (hadm : σ.IsAdmissible) :
    ∃ c : rationalPoints A.toGrp →* ℂˣ, ∀ t,
      σ.representation (rationalPoints.map a t) = (c t : ℂ) • (1 : Module.End ℂ σ) := by
  obtain ⟨chi, ⟨-, hchi⟩, -⟩ := admissibleSchur_centralCharacter σ.representation hadm hirr
  refine ⟨chi.comp ((rationalPoints.map a).codRestrict _
    ha.isCentralSplitTorus.isCentral.map_mem_center), fun t => ?_⟩
  apply LinearMap.ext
  intro v
  exact hchi ⟨_, ha.isCentralSplitTorus.isCentral.map_mem_center t⟩ v

end Central

namespace GeometricLemmaIntersectionDatum

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance genericRegularityPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : M ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}

/-- On a non-identity same-Levi piece, a nonzero polynomial in the unramified
coordinates of `M(F)` separates, off its zero locus, every generalized character
of the split component on the piece of `σψ` from the character `c · ψ|_A`; the
piece also has a finite-dimensional action quotient. -/
theorem exists_generic_piece_separation
    (hG : IsConnectedReductive G) (hLevi : l ≫ p = lQ ≫ q)
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
    (hz : DoubleCoset.mk (pointImage p) (pointImage q) z ≠ identityParabolicDoubleCoset p q)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
    (ha : IsSplitComponent a) (c : rationalPoints A.toGrp →* ℂˣ) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M), σ.IsIrreducible → σ.IsAdmissible →
      ∃ poly : MvPolynomial (Fin (Plancherel.rationalImageRank M)) ℂ, poly ≠ 0 ∧
        ∀ ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hl.isConnectedReductive poly,
          Module.Finite ℂ (actionQuotient ((D.pieceFunctor.obj
            (σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))).ρ.comp
              (rationalPoints.map a))) ∧
          ∀ χ, IsGeneralizedEigencharacter ((D.pieceFunctor.obj
            (σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))).ρ.comp
              (rationalPoints.map a)) χ →
            χ ≠ c * ψ.val.toMonoidHom.comp (rationalPoints.map a) := by
  have hM := hl.isConnectedReductive
  have := hM.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  let := leviPointTopology D.l' D.hl'
  intro σ hirr hadm
  obtain ⟨A', a', f₀, ha', hf₀⟩ := D.exists_isSplitComponent_factor ha
  let f : A ⟶ A' := Additive.ofMul f₀
  have hf : CommGroupScheme.groupHom f ≫ a' ≫ D.lQ' ≫ D.q' = a := hf₀
  have hb : (CommGroupScheme.groupHom f ≫ a') ≫ D.lQ' ≫ D.q' = a := by
    simpa only [Category.assoc] using hf
  obtain ⟨t, ht⟩ := sameLeviPieceStrictDisplacement k G hG P M N Q U p l r hp hl hr hmul
    q lQ rQ hq hlQ hrQ hmulQ hLevi A a ha z hz D _ hb
  simp only [Category.assoc] at ht
  have hJ : ∀ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M), ρ.IsIrreducible → ρ.IsAdmissible →
      ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj ρ).IsAdmissible ∧
      Module.Finite (MonoidAlgebra ℂ (rationalPoints D.M'))
        ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj
          ρ).representation.asModule := by
    intro ρ hρi hρa
    exact ⟨isAdmissible_comp_continuousMulEquiv
      ((jacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj ρ).representation
      (leviPointsEquiv D.p' D.l' D.hp' D.hl')
      (arbitraryParabolicJacquetAdmissibility.{u, v} k M hM D.P' D.M' D.N' D.p' D.l' D.r'
        D.hp' D.hl' D.hr' D.hmul' ρ hρa),
      leviJacquetFiniteType.{u, v} k M hM D.P' D.M' D.N' D.p' D.l' D.r' D.hp' D.hl' D.hr'
        D.hmul' ρ (moduleFinite_asModule_of_isIrreducible ρ.representation hρi)⟩
  obtain ⟨hJa, hJf⟩ := hJ σ hirr hadm
  have hΘ := finite_normalizedJacquetExponents_of_leviJacquet D.p' D.l' D.r' D.hp' D.hl' D.hr'
    D.hmul' (ha'.comp_iso D.φ) σ hJa hJf
  choose P hP0 hPsep using fun θ : rationalPoints A'.toGrp →* ℂˣ =>
    Plancherel.exists_ne_zero_rationalUnramifiedPrincipalOpen_apply_ne M hM _ _ ht
      ((θ (rationalPoints.map (CommGroupScheme.groupHom f) t) : ℂ) * ((c t)⁻¹ : ℂˣ))
  refine ⟨∏ θ ∈ hΘ.toFinset, P θ, Finset.prod_ne_zero_iff.mpr fun θ _ => hP0 θ, ?_⟩
  intro ψ hψ
  have hτirr := (SmoothRep.isIrreducible_twist_iff ψ.val.toMonoidHom
    (Plancherel.unramifiedCharacter_isOpen_ker _ ψ) σ).mpr hirr
  have hτadm := (SmoothRep.isAdmissible_twist_iff ψ.val.toMonoidHom
    (Plancherel.unramifiedCharacter_isOpen_ker _ ψ) σ).mpr hadm
  obtain ⟨hτJa, hτJf⟩ := hJ _ hτirr hτadm
  refine ⟨D.finite_actionQuotient_piece ha _ hb _ hτJa hτJf, ?_⟩
  intro χ hχ hχeq
  obtain ⟨θ, hθ, hχθ, -⟩ :=
    D.exists_untwisted_sourceJacquetExponent_of_twisted_piece p l r hp hl hr hmul ha ha' f hf σ ψ
      hτJa χ hχ
  have hψθ : ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hM (P θ) := by
    rw [Plancherel.mem_rationalUnramifiedPrincipalOpen] at hψ ⊢
    rw [map_prod] at hψ
    exact Finset.prod_ne_zero_iff.mp hψ θ (hΘ.mem_toFinset.mpr hθ)
  apply hPsep θ ψ hψθ
  have h1 := DFunLike.congr_fun (hχθ.symm.trans hχeq) t
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply] at h1
  rw [← Units.val_mul, ← Units.val_mul]
  congr 1
  calc ψ.val (rationalPoints.map a t)
      = (c t)⁻¹ * (c t * ψ.val (rationalPoints.map a t)) := by rw [inv_mul_cancel_left]
    _ = (c t)⁻¹ * (θ (rationalPoints.map (CommGroupScheme.groupHom f) t) *
          ψ.val (rationalPoints.map
            (CommGroupScheme.groupHom f ≫ a' ≫ D.φ.hom ≫ D.l' ≫ D.p') t)) := by
        exact congrArg ((c t)⁻¹ * ·) h1.symm
    _ = θ (rationalPoints.map (CommGroupScheme.groupHom f) t) * (c t)⁻¹ *
          ψ.val (rationalPoints.map
            (CommGroupScheme.groupHom f ≫ a' ≫ D.φ.hom ≫ D.l' ≫ D.p') t) := by
        rw [mul_left_comm, ← mul_assoc]

end GeometricLemmaIntersectionDatum

/-- For represented parabolics `P = MN` and `Q = MU` with the same Levi subgroup and an
irreducible admissible representation `σ` of `M(F)`, the twist `σψ` is `PQ`-regular for a
split component off the zero locus of a nonzero polynomial in the unramified coordinates. -/
theorem exists_generic_isPQRegular
    (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N Q U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r))
      (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
      (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
      (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
      (hmulQ : IsIso (subgroupMultiplication lQ rQ)),
      l ≫ p = lQ ≫ q →
      ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M),
        IsSplitComponent a →
        letI := leviPointTopology l hl
        haveI := leviPoints_nonarchimedeanGroup p l hp hl
        ∀ (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)), σ.IsIrreducible → σ.IsAdmissible →
          ∃ poly : MvPolynomial (Fin (Plancherel.rationalImageRank M)) ℂ, poly ≠ 0 ∧
            ∀ ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hl.isConnectedReductive poly,
              IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a
                (σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)) := by
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hsame A a ha
  let := leviPointTopology l hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro σ hirr hadm
  obtain ⟨m, c₀, z, hz, E, -⟩ := representedGeometricLemma.{u, v} k G hG P M N Q M U
    p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
  let z' : parabolicDoubleCosets p q → rationalPoints G := fun w => z (c₀.symm w)
  have hz' : ∀ w, DoubleCoset.mk (pointImage p) (pointImage q) (z' w) = w :=
    fun w => (hz _).trans (c₀.apply_symm_apply w)
  let D' : ∀ w, Geometric.BruhatLT (pointImage p) (pointImage q) w
      (identityParabolicDoubleCoset p q) →
      GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ (z' w) :=
    fun w _ => E (c₀.symm w)
  obtain ⟨n, cc, s, e⟩ := pqRegularityPieceFiltration.{u, v} k G hG P M N Q U
    p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hsame z' hz' D'
  obtain ⟨cσ, hcσ⟩ := exists_splitComponent_scalar ha σ hirr hadm
  have hsep := fun i : Fin n =>
    GeometricLemmaIntersectionDatum.exists_generic_piece_separation hG hsame
      (D' (cc i).val (cc i).property) (by rw [hz']; exact (cc i).property.2) ha cσ
      σ hirr hadm
  choose Pi hP0 hPψ using hsep
  refine ⟨∏ i, Pi i, Finset.prod_ne_zero_iff.mpr fun i _ => hP0 i, ?_⟩
  intro ψ hψ
  have hψi : ∀ i, ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hl.isConnectedReductive
      (Pi i) := by
    intro i
    rw [Plancherel.mem_rationalUnramifiedPrincipalOpen] at hψ ⊢
    rw [map_prod] at hψ
    exact Finset.prod_ne_zero_iff.mp hψ i (Finset.mem_univ i)
  set τ := σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ) with hτ
  have hτa : ∀ t, (τ.obj.ρ.comp (rationalPoints.map a)) t =
      ((cσ * ψ.val.toMonoidHom.comp (rationalPoints.map a)) t : ℂ) • 1 := by
    intro t
    change (ψ.val.toMonoidHom (rationalPoints.map a t) : ℂ) •
      σ.representation (rationalPoints.map a t) = _
    rw [hcσ t, smul_smul, MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, mul_comm]
  have : Module.Finite ℂ (actionQuotient (τ.obj.ρ.comp (rationalPoints.map a))) :=
    CentralActionQuotient.finite_actionQuotient_of_scalar _ _ hτa
  have : ∀ i, Module.Finite ℂ (actionQuotient
      (((D' (cc i).val (cc i).property).pieceFunctor.obj τ).ρ.comp (rationalPoints.map a))) :=
    fun i => (hPψ i ψ (hψi i)).1
  exact pqRegularity_of_disjoint_generalizedCharacters p l r hp hr hl hmul q lQ rQ hq hrQ hlQ
    hmulQ a s (fun i => (D' (cc i).val (cc i).property).pieceFunctor) e τ
    (fun i => Set.disjoint_left.mpr fun χ hχ hχi => (hPψ i ψ (hψi i)).2 χ hχi
      (CentralActionQuotient.eq_of_isGeneralizedEigencharacter_of_scalar _ _ hτa χ hχ))

end Langlands.Aubert.General.RepresentedParabolic
