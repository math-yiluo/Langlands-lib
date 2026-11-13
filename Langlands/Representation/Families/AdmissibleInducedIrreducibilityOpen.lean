import Langlands.Representation.Families.SubrepDetectionPrincipalOpen
import Langlands.Representation.Families.InducedTwistsDetectionJacquetLift
import Langlands.Representation.Families.InducedTwistsDetectionReduction
import Langlands.Representation.Families.InducedIrreducibilityOpenAssembly
import Langlands.Representation.Exponents.LeviInductionDualityAdjunction
import Langlands.Representation.Exponents.LeviParabolicFunctorsExactProof
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityReduction
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactProof
import Langlands.Representation.Category.ExactFunctor
import Langlands.Representation.Category.Twist
import Langlands.Representation.Compact.SurjectivityProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof

/-! # Irreducibility neighborhoods for induced twists of admissible representations

Let `ρ` be an irreducible admissible smooth representation of the rational points
of a Levi `M` of a parabolic `P = MN`. One compact open subgroup `K` of `G(k)`
detects every `i_P^G(ρ ⊗ ψ)` through subrepresentations: every nonzero
subrepresentation has a nonzero `K`-fixed vector, by Frobenius reciprocity and
the weak Jacquet lemma, and every subrepresentation containing the `K`-fixed
vectors is everything, by applying the first statement to the contragredient
`i_P^G(ρ ⊗ ψ)~ ≅ i_P^G((ρ ⊗ ψ)~)`. With the universal unramified family this
gives the conclusion of Renard VI.8.4 for admissible `ρ`.
-/

set_option autoImplicit false

noncomputable section

universe u v uR uG uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily.AdmissibleInducedIrreducibilityOpen

open Langlands.GroupScheme Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic
open SubrepDetectionPrincipalOpen InducedTwistsDetection

/-- The underlying intertwiner of an isomorphism of smooth representations is
injective. -/
theorem hom_injective_of_iso {R : Type uR} {G : Type uG} [CommRing R] [Group G]
    [TopologicalSpace G] {A B : SmoothRep.{uR, uG, uV} R G} (e : A ≅ B) :
    Function.Injective (SmoothRep.hom e.hom) := by
  intro x y hxy
  have hx : SmoothRep.hom (e.hom ≫ e.inv) x = x := by rw [e.hom_inv_id]; rfl
  have hy : SmoothRep.hom (e.hom ≫ e.inv) y = y := by rw [e.hom_inv_id]; rfl
  rw [← hx, ← hy]
  change SmoothRep.hom e.inv (SmoothRep.hom e.hom x) = SmoothRep.hom e.inv (SmoothRep.hom e.hom y)
  rw [hxy]

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance admissibleOpenPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Frobenius reciprocity and the weak Jacquet lemma: if `K` has an Iwahori
contraction relative to `P = MN`, the Levi points in `K` lie in a compact open
`C`, and `σ` is irreducible with a nonzero `C`-fixed vector, then every nonzero
subrepresentation of `i_P^G σ` has a nonzero `K`-fixed vector, provided
`(i_P^G σ)^K` is finite dimensional. -/
theorem leviInduction_subrep_exists_fixed
    (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
    haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ (K : OpenSubgroup (rationalPoints G)) (_hK : IsCompact (K : Set (rationalPoints G)))
      (X : Subgroup (rationalPoints G)) (g : rationalPoints G)
      (_hcon : Jacquet.IsIwahoriContraction K (pointImage (r ≫ p)) (pointImage (l ≫ p)) X g)
      (C : OpenSubgroup (rationalPoints M)) (_hC : IsCompact (C : Set (rationalPoints M)))
      (_hKC : ∀ m : rationalPoints M, rationalPoints.map (l ≫ p) m ∈ K → m ∈ C)
      (σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M)) (_hσ : σ.IsIrreducible)
      (_hσC : ∃ v₀ : σ, v₀ ∈ fixedVectors σ.representation C.toSubgroup ∧ v₀ ≠ 0)
      (_hfin : FiniteDimensional ℂ (fixedVectors
        ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj σ).representation
          K.toSubgroup))
      (S : Subrepresentation
        ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj σ).representation),
      S ≠ ⊥ → ∃ w ∈ S.toSubmodule, w ∈ fixedVectors
        ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj σ).representation
          K.toSubgroup ∧ w ≠ 0 := by
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro K hK X g hcon C hC hKC σ hσ hσC hfin S hS
  obtain ⟨v₀, hv₀C, hv₀⟩ := hσC
  let I := leviInductionFunctor.{u, max u v} p l r hp hr hl hmul
  let J := leviJacquetFunctor.{u, max u v} p l r hp hr hl hmul
  let adj : J ⊣ I := leviFirstAdjointnessAdjunction.{u, v} p l r hp hl hr hmul
  let π := I.obj σ
  let W := SmoothRep.subrepresentation π S
  let incl : W ⟶ π := SmoothRep.subtype π S
  -- The inclusion of `S` is nonzero.
  have hincl0 : incl ≠ 0 := by
    intro h
    apply hS
    apply Subrepresentation.toSubmodule_injective
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    have hx0 : SmoothRep.hom incl ⟨x, hx⟩ = 0 := by rw [h]; rfl
    exact hx0
  -- Its Frobenius adjoint `J W ⟶ σ` is nonzero, hence surjective.
  have hIexact : SmoothRep.PreservesShortExact I :=
    (leviParabolicFunctorsExact.{u, max u v} k G hG P M U p l r hp hl hr hmul).1
  have : I.PreservesZeroMorphisms := hIexact.preservesZeroMorphisms
  let φ : J.obj W ⟶ σ := (adj.homEquiv W σ).symm incl
  have hφ0 : φ ≠ 0 := by
    intro hφ
    apply hincl0
    have hinclφ : incl = adj.homEquiv W σ φ := ((adj.homEquiv W σ).apply_symm_apply incl).symm
    rw [hinclφ, hφ, Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero]
  have : σ.representation.IsIrreducible := hσ
  have hφsurj : Function.Surjective (SmoothRep.hom φ) := by
    rcases Representation.IsIrreducible.surjective_or_eq_zero (SmoothRep.hom φ) with h | h
    · exact h
    · exact absurd (SmoothRep.hom_ext' (h.trans rfl)) hφ0
  -- Lift `v₀` to a nonzero `C`-fixed vector of the Jacquet module of `W`.
  obtain ⟨y, hy⟩ := Compact.fixedVectorSurjectivity (rationalPoints M) (J.obj W) σ
    (J.obj W).representation σ.representation (J.obj W).isSmooth σ.isSmooth C hC
    (SmoothRep.hom φ) hφsurj ⟨v₀, hv₀C⟩
  have hyv : SmoothRep.hom φ y.val = v₀ := congrArg Subtype.val hy
  have hy0 : y.val ≠ 0 := by
    intro hz
    apply hv₀
    rw [← hyv, hz, map_zero]
  -- It is fixed by the Levi points lying in `K`.
  let N' := pointImage (r ≫ p)
  let M' := pointImage (l ≫ p)
  have hN' : IsClosed (N' : Set (rationalPoints G)) :=
    isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup
  have hM' : IsClosed (M' : Set (rationalPoints G)) :=
    isClosed_pointImage_comp p l hp.isClosedSubgroup hl.isClosedSubgroup
  have hMN' : M' ≤ Subgroup.normalizer N' := pointImage_le_normalizer p l r hr
  have hyfix : y.val ∈ fixedVectors
      ((normalizedJacquetFunctor N' M' hN' hMN').obj W).representation
      (K.toSubgroup.comap M'.subtype) := by
    rintro ⟨⟨x, ⟨m, rfl⟩⟩, hxK⟩
    have hmK : rationalPoints.map (l ≫ p) m ∈ K := hxK
    have hfixm : (J.obj W).representation m y.val = y.val := y.property ⟨m, hKC m hmK⟩
    change ((normalizedJacquetFunctor N' M' hN' hMN').obj W).representation
      (leviPointsEquiv p l hp hl m) y.val = y.val at hfixm
    exact hfixm
  -- `W^K` is finite dimensional.
  have hfinW : FiniteDimensional ℂ (fixedVectors W.representation K.toSubgroup) := by
    let iK := Compact.fixedVectorMap W.representation π.representation (SmoothRep.hom incl)
      K.toSubgroup
    have hiK : Function.Injective iK := by
      intro a b hab
      apply Subtype.ext
      apply SmoothRep.subtype_injective π S
      have h : (iK a).val = (iK b).val := congrArg Subtype.val hab
      exact h
    exact Module.Finite.of_injective iK hiK
  -- The weak Jacquet lemma gives a nonzero `K`-fixed vector of `W`.
  obtain ⟨x, hx, hx0⟩ := exists_fixed_of_normalizedJacquet_fixed N' M' X hN' hMN' hM' K hK g
    hcon W hfinW ⟨y.val, hyfix, hy0⟩
  refine ⟨SmoothRep.hom incl x, x.property, map_mem_fixedVectors (SmoothRep.hom incl) hx, ?_⟩
  intro hz
  exact hx0 (SmoothRep.subtype_injective π S (hz.trans (map_zero _).symm))

/-- Under the hypotheses of `leviInduction_subrep_exists_fixed`, for admissible
`σ` the induced representation `i_P^G σ` is generated by its `K`-fixed vectors:
a quotient without `K`-fixed vectors has a contragredient without `K`-fixed
vectors, which embeds in `i_P^G σ~`. -/
theorem leviInduction_fixedVectors_generate_of_admissible
    (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
    haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ (K : OpenSubgroup (rationalPoints G)) (_hK : IsCompact (K : Set (rationalPoints G)))
      (X : Subgroup (rationalPoints G)) (g : rationalPoints G)
      (_hcon : Jacquet.IsIwahoriContraction K (pointImage (r ≫ p)) (pointImage (l ≫ p)) X g)
      (C : OpenSubgroup (rationalPoints M)) (_hC : IsCompact (C : Set (rationalPoints M)))
      (_hKC : ∀ m : rationalPoints M, rationalPoints.map (l ≫ p) m ∈ K → m ∈ C)
      (σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M)) (_hσ : σ.IsIrreducible)
      (_hσadm : σ.IsAdmissible)
      (_hσC : ∃ v₀ : σ, v₀ ∈ fixedVectors σ.representation C.toSubgroup ∧ v₀ ≠ 0)
      (S : Subrepresentation
        ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj σ).representation),
      fixedVectors ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj σ).representation
        K.toSubgroup ≤ S.toSubmodule → S = ⊤ := by
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro K hK X g hcon C hC hKC σ hσ hσadm hσC S hS
  by_contra hne
  let I := leviInductionFunctor.{u, max u v} p l r hp hr hl hmul
  let π := I.obj σ
  let Q := SmoothRep.quotient π S
  let q : π ⟶ Q := SmoothRep.mkQ π S
  -- The quotient has no nonzero `K`-fixed vector.
  have hQK : ∀ x ∈ fixedVectors Q.representation K.toSubgroup, x = 0 := by
    intro x hx
    obtain ⟨y, hy⟩ := Compact.fixedVectorSurjectivity (rationalPoints G) π Q
      π.representation Q.representation π.isSmooth Q.isSmooth K hK (SmoothRep.hom q)
      (SmoothRep.mkQ_surjective π S) ⟨x, hx⟩
    have hyx : SmoothRep.hom q y.val = x := congrArg Subtype.val hy
    have hyS : y.val ∈ S.toSubmodule := hS y.property
    rw [← hyx]
    exact (Submodule.Quotient.mk_eq_zero S.toSubmodule).mpr hyS
  -- The quotient is nonzero, so it has a nonzero smooth functional.
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : Q, x₀ ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hne
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro y _
    exact (Submodule.Quotient.mk_eq_zero S.toSubmodule).mp (hno (SmoothRep.hom q y))
  obtain ⟨L₀, hL₀⟩ := Q.isSmooth x₀
  obtain ⟨L, hLc, hLL₀⟩ := Jacquet.exists_isCompact_openSubgroup_subset
    (L₀.isOpen.mem_nhds L₀.one_mem)
  have hx₀L : x₀ ∈ fixedVectors Q.representation L.toSubgroup :=
    fun h => hL₀ ⟨h.val, hLL₀ h.property⟩
  obtain ⟨lam, -, hlam0⟩ := exists_contragredient_fixed_ne_zero Q L hLc hx₀L hx₀
  have hQdK := contragredient_fixed_eq_zero Q K hK hQK
  -- The contragredient of the quotient embeds in `i_P^G σ~`.
  obtain ⟨α⟩ := nonempty_leviInductionContragredientIso.{u, v} hG p l r hp hl hr hmul
  let Φ : π.contragredient ≅ I.obj σ.contragredient := α.app (Opposite.op σ)
  let ψ : Q.contragredient ⟶ I.obj σ.contragredient := SmoothRep.contragredientHom q ≫ Φ.hom
  have hψinj : Function.Injective (SmoothRep.hom ψ) := by
    intro a b hab
    apply contragredientMap_injective_of_surjective (SmoothRep.hom q)
      (SmoothRep.mkQ_surjective π S)
    exact hom_injective_of_iso Φ hab
  let T := (SmoothRep.hom ψ).range
  have hT : T ≠ ⊥ := by
    intro hT
    have hmem : SmoothRep.hom ψ lam ∈ T.toSubmodule := ⟨lam, rfl⟩
    rw [hT] at hmem
    have hz : SmoothRep.hom ψ lam = 0 := hmem
    exact hlam0 (hψinj (hz.trans (map_zero _).symm))
  -- The hypotheses of the subrepresentation statement hold for `σ~`.
  have hcofM : CompactOpenCofinal (rationalPoints M) := fun K' => by
    obtain ⟨L', hL'c, hL'K'⟩ := Jacquet.exists_isCompact_openSubgroup_subset
      (K'.isOpen.mem_nhds K'.one_mem)
    exact ⟨L', hL'c, fun x hx => hL'K' hx⟩
  have hσd : σ.contragredient.IsIrreducible :=
    (SmoothRep.isIrreducible_contragredient_iff hcofM σ hσadm).mpr hσ
  have hσdadm : σ.contragredient.IsAdmissible :=
    (SmoothRep.isAdmissible_contragredient_iff hcofM σ).mpr hσadm
  obtain ⟨v₀, hv₀C, hv₀⟩ := hσC
  have hσdC := exists_contragredient_fixed_ne_zero σ C hC hv₀C hv₀
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : CompactSpace (Induction.LeftQuotient (pointImage p)) :=
    arbitraryParabolicQuotientCompact k G hG P p hp
  have hIadm : (I.obj σ.contragredient).IsAdmissible :=
    leviInductionFunctor_obj_isAdmissible p l r hp hl hr hmul σ.contragredient hσdadm
  have hfin : FiniteDimensional ℂ
      (fixedVectors (I.obj σ.contragredient).representation K.toSubgroup) := hIadm.2 K
  obtain ⟨w, hwT, hwK, hw0⟩ := leviInduction_subrep_exists_fixed.{u, v} hG p l r hp hl hr hmul K hK
    X g hcon C hC hKC σ.contragredient hσd hσdC hfin T hT
  obtain ⟨lam₁, rfl⟩ := hwT
  -- Its preimage is a `K`-fixed functional on the quotient, hence zero.
  have hlam₁K : lam₁ ∈ fixedVectors Q.contragredient.representation K.toSubgroup := by
    intro h
    apply hψinj
    change SmoothRep.hom ψ (Q.contragredient.representation h.val lam₁) = SmoothRep.hom ψ lam₁
    rw [Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom ψ) h.val lam₁]
    exact hwK h
  apply hw0
  rw [hQdK lam₁ hlam₁K, map_zero]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- Subrepresentation detection passes from the induction of the universe-lifted
inducing representation to the induction of the original one. -/
theorem leviInduction_subrepDetected_of_universeLift
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (hp : IsParabolicSubgroup p)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) (hl : IsRationalLeviSubgroup l)
    (hmul : IsIso (subgroupMultiplication l r)) :
    letI := leviPointTopology l hl
    ∀ (τ : SmoothRep.{0, u, v} ℂ (rationalPoints M)) (K : Subgroup (rationalPoints G)),
      IsSubrepDetected ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj
          (SmoothRep.universeLift.{u} τ)).representation K →
        IsSubrepDetected ((leviInductionFunctor.{u, v} p l r hp hr hl hmul).obj τ).representation
          K := by
  let := leviPointTopology l hl
  intro τ K hdet
  let e := leviPointsEquiv p l hp hl
  let E : (SmoothRep.pullback e.symm τ).representation.Equiv
      (SmoothRep.pullback e.symm (SmoothRep.universeLift.{u} τ)).representation :=
    Representation.Equiv.mk (SmoothRep.universeLiftEquiv.{u} τ).toLinearEquiv
      (fun x => (SmoothRep.universeLiftEquiv.{u} τ).isIntertwining' (e.symm x))
  let F := normalizedInductionEquivOfEquiv
    (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup) E
  exact IsSubrepDetected.of_equiv F.symm hdet

/-- For an irreducible admissible `ρ`, one compact open subgroup of `G(k)`
detects every induced unramified twist `i_P^G(ρ ⊗ ψ)` through
subrepresentations. -/
theorem exists_uniform_subrepDetected
    (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
    haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M), ρ.IsIrreducible → ρ.IsAdmissible →
      ∃ K : OpenSubgroup (rationalPoints G), IsCompact (K : Set (rationalPoints G)) ∧
        ∀ ψ : Plancherel.unramifiedCharacters
            (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul),
          IsSubrepDetected ((leviInductionFunctor.{u, v} p l r hp hr hl hmul).obj
            (ρ.twist ψ.val.toMonoidHom
              (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))).representation
            K.toSubgroup := by
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro ρ hρ hadm
  -- A nonzero vector of `ρ` fixed by a compact open subgroup `Cρ` of `M(k)`.
  obtain ⟨v₀, hv₀⟩ := exists_ne_zero_of_isIrreducible hρ
  obtain ⟨Kρ, hKρ⟩ := ρ.isSmooth v₀
  obtain ⟨Cρ, hCρc, hCρ⟩ := Jacquet.exists_isCompact_openSubgroup_subset
    (Kρ.isOpen.mem_nhds Kρ.one_mem)
  -- An open subset `O` of `G(k)` whose Levi points lie in `Cρ`.
  have hind : Topology.IsInducing (fun m : rationalPoints M => rationalPoints.map (l ≫ p) m) :=
    Topology.IsInducing.subtypeVal.comp (leviPointsEquiv p l hp hl).toHomeomorph.isInducing
  obtain ⟨O, hO, hOpre⟩ := hind.isOpen_iff.mp Cρ.isOpen
  have h1O : (1 : rationalPoints G) ∈ O := by
    have h1 : (1 : rationalPoints M) ∈ (fun m => rationalPoints.map (l ≫ p) m) ⁻¹' O := by
      rw [hOpre]
      exact Cρ.one_mem
    simpa using h1
  -- A compact open `K ⊆ O` with an Iwahori contraction relative to `P = MN`.
  obtain ⟨χ, hP, hM⟩ :=
    DynamicLeviConjugacy.exists_cocharacter_parabolic_levi parabolicDynamic
      dynamicGeometricUnipotentRadical hG hp hl
  have hN := pointImage_radical_eq_dynamic dynamicGeometricUnipotentRadical hG χ hp hP hr
  have hL : pointImage (l ≫ p) =
      (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) :=
    congrArg (fun F : SubgroupFunctor G => F.carrier (Over.mk (𝟙 _))) hM
  obtain ⟨g, hBasis⟩ := RationalPointFamily.dynamic_hasOppositeIwahoriContractionBasis G hG χ
  obtain ⟨K, hKc, hKO, hcon, -⟩ := hBasis O hO h1O
  rw [← hN, ← hL] at hcon
  have hKC : ∀ m : rationalPoints M, rationalPoints.map (l ≫ p) m ∈ K → m ∈ Cρ := by
    intro m hm
    have hmO : m ∈ (fun m => rationalPoints.map (l ≫ p) m) ⁻¹' O := hKO hm
    rw [hOpre] at hmO
    exact hmO
  refine ⟨K, hKc, fun ψ => ?_⟩
  let τ := ρ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)
  let σ := SmoothRep.universeLift.{u} τ
  have hfix : SmoothRep.universeLiftEquiv τ v₀ ∈
      fixedVectors σ.representation Cρ.toSubgroup := by
    rintro ⟨m, hmC⟩
    have hψ : ψ.val m = 1 :=
      ψ.property (Plancherel.compactSubgroup_le_rationalCommonNormKernel M Cρ.toSubgroup hCρc hmC)
    have hρm : ρ.representation m v₀ = v₀ := hKρ ⟨m, hCρ hmC⟩
    show ULift.up (((ψ.val.toMonoidHom m : ℂˣ) : ℂ) • ρ.representation m v₀) = ULift.up v₀
    rw [hρm]
    change ULift.up (((ψ.val m : ℂˣ) : ℂ) • v₀) = ULift.up v₀
    rw [hψ, Units.val_one, one_smul]
  have hv₀' : SmoothRep.universeLiftEquiv.{u} τ v₀ ≠ 0 := by
    intro hz
    apply hv₀
    exact (SmoothRep.universeLiftEquiv τ).injective (hz.trans (map_zero _).symm)
  have hσ : σ.IsIrreducible :=
    (SmoothRep.isIrreducible_universeLift_iff τ).mpr
      ((SmoothRep.isIrreducible_twist_iff _ _ ρ).mpr hρ)
  have hσadm : σ.IsAdmissible :=
    (SmoothRep.isAdmissible_universeLift_iff τ).mpr
      ((SmoothRep.isAdmissible_twist_iff _ _ ρ).mpr hadm)
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : CompactSpace (Induction.LeftQuotient (pointImage p)) :=
    arbitraryParabolicQuotientCompact k G hG P p hp
  have hfin : FiniteDimensional ℂ (fixedVectors
      ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj σ).representation
        K.toSubgroup) :=
    (leviInductionFunctor_obj_isAdmissible p l r hp hl hr hmul σ hσadm).2 K
  have hdet : IsSubrepDetected
      ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj σ).representation
        K.toSubgroup :=
    ⟨fun S hS => leviInduction_subrep_exists_fixed.{u, v} hG p l r hp hl hr hmul K hKc _ g hcon
        Cρ hCρc hKC σ hσ ⟨_, hfix, hv₀'⟩ hfin S hS,
      leviInduction_fixedVectors_generate_of_admissible.{u, v} hG p l r hp hl hr hmul K hKc _ g hcon
        Cρ hCρc hKC σ hσ hσadm ⟨_, hfix, hv₀'⟩⟩
  exact leviInduction_subrepDetected_of_universeLift p l r hp hr hl hmul τ K.toSubgroup hdet

end Langlands.Renard.AlgebraicFamily.AdmissibleInducedIrreducibilityOpen

namespace Langlands.Renard.AlgebraicFamily

open Langlands.GroupScheme Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic
open AdmissibleInducedIrreducibilityOpen

/-- **Renard VI.8.4 for admissible inducing representations.** For an
irreducible admissible smooth representation `ρ` of the rational points of a
Levi `M` of a parabolic `P = MN`, if `i_P^G(ρ ⊗ ψ₀)` is irreducible then it stays
irreducible on a principal Zariski open neighborhood of `ψ₀` in the unramified
characters of `M`. -/
theorem admissibleInducedIrreducibilityOpen
    (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M), ρ.IsIrreducible → ρ.IsAdmissible →
        ∀ ψ₀ : Plancherel.unramifiedCharacters
            (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul),
          ((leviInductionFunctor p l r hp hr hl hmul).obj
              (ρ.twist ψ₀.val.toMonoidHom
                (Plancherel.unramifiedCharacter_isOpen_ker _ ψ₀))).IsIrreducible →
            ∃ f : MvPolynomial (Fin (Plancherel.rationalImageRank M)) ℂ,
              ψ₀ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hl.isConnectedReductive f ∧
                ∀ ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hl.isConnectedReductive f,
                  ((leviInductionFunctor p l r hp hr hl hmul).obj
                    (ρ.twist ψ.val.toMonoidHom
                      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))).IsIrreducible := by
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have : LocallyOfFiniteType M.X.hom := by
    have := hl.isConnectedReductive.smooth
    infer_instance
  intro ρ hρ hadm ψ₀ hirr₀
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : CompactSpace (Induction.LeftQuotient (pointImage p)) :=
    arbitraryParabolicQuotientCompact k G hG P p hp
  obtain ⟨K, hK, hKdet⟩ := exists_uniform_subrepDetected hG p l r hp hl hr hmul ρ hρ hadm
  exact SubrepDetectionPrincipalOpen.exists_polynomial_principal_neighborhood_of_family_of_subrepDetected
    (ActualLevi.universalFamily p l r hp hl hr hmul ρ) K hK M hl.isConnectedReductive
    (ActualLevi.regularAlgebraEquiv p l hp hl).symm _
    (InducedIrreducibilityOpenAssembly.universalFamily_isGlobalCoefficientFamily hG p l r hp hl
      hr hmul ρ hadm) hKdet ψ₀ hirr₀

end Langlands.Renard.AlgebraicFamily
