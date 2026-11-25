import Langlands.GaloisCohomology.CompactSupport.TateModified.NineTerm
import Langlands.GaloisCohomology.Global.RealPlaces.LocalDuality
import Langlands.GaloisCohomology.Global.Units.Brauer
import Langlands.GaloisCohomology.Global.Dimension.Proof
import Langlands.GaloisCohomology.Global.Localization
import Langlands.GaloisCohomology.Local.EulerCharacteristic.Coprime

/-!
# The trace of Poitou–Tate duality for `G_S`

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places of `K`,
`G_S = Gal(K_S/K)` and `ι : PlaceEmbeddings K Ω`. This file fixes the data in which the duality
theorems of Poitou and Tate for `G_S` are stated:

* the family of localization homomorphisms `G_{K_v} → G_S` at the places `v ∈ S` (`localFamily`)
  and at the real places (`realFamily`);
* the dualizing module `μ_N = μ_N(K_S)` (`dualizingModule`), for `N ≥ 1`;
* the local invariants `H²(K_v, μ_N) → ℚ/ℤ` (`invariantAt`), the image of the class in
  `H²(K_v, K̄_vˣ)` under the invariant of local class field theory, and the same at the real places
  (`realInvariantAt`, with the real invariant of the Brauer sequence);
* the trace `Ĥ_c³(G_S, μ_N) → ℤ/N` (`trace`) on the cohomology with compact support in which degree
  `0` at the real places is Tate's `Ĥ⁰`. It is characterized by `trace_localToCompact`: on the image
  of `∏_{v ∈ S} H²(K_v, μ_N) × ∏_{w real} H²(K_w, μ_N)` it is the sum of the local invariants.

The trace exists because the sum of the local invariants vanishes on the localizations of a global
class (`sumInvariants_globalToLocal`): a class of `H²(G_S, μ_N)` maps to the Brauer group of `K`
with zero invariants outside `S`, and the sum of all invariants of a global Brauer class is zero
(the reciprocity law of the Brauer sequence, `localInvariant_finite_support_and_sum_eq_zero`). It is
chosen as an extension of this sum to `Ĥ_c³`; that the extension is unique follows from the
surjectivity of `∏ H²(·, μ_N) → Ĥ_c³(G_S, μ_N)`, a consequence of the duality theorem.
-/

namespace Langlands.GaloisCohomology.PoitouTate

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

noncomputable section

section Instances

/-- The real places of a number field, as a finite type. -/
noncomputable instance fintypeRealPlaces (K : Type u) [Field K] [NumberField K] :
    Fintype {w : InfinitePlace K // w.IsReal} :=
  Fintype.ofFinite _

/-- The Galois group of the algebraic closure of the completion at an infinite place, as a finite
type. -/
noncomputable instance fintypeClosureGalois {K : Type u} [Field K] [NumberField K]
    (w : InfinitePlace K) : Fintype Gal(AlgebraicClosure w.Completion/w.Completion) :=
  Fintype.ofFinite _

end Instances

section Families

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- The localization homomorphisms `G_{K_v} → G_S` at the places `v ∈ S`. -/
abbrev localFamily (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) :
    ∀ v : S, Gal(AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)/
      (v : HeightOneSpectrum (𝓞 K)).adicCompletion K) →ₜ* GaloisGroupUnramifiedOutside K Ω S :=
  fun v => localizationHom ι S v

/-- The localization homomorphisms `G_{K_w} → G_S` at the real places `w` (finite groups of order
two). -/
abbrev realFamily (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) :
    ∀ w : {w : InfinitePlace K // w.IsReal}, Gal(AlgebraicClosure w.1.Completion/w.1.Completion) →ₜ*
      GaloisGroupUnramifiedOutside K Ω S :=
  fun w => realLocalizationHom ι S w.1

variable (K Ω) in
/-- The dualizing module `μ_N(K_S)` of `G_S`. -/
abbrev dualizingModule (S : Set (HeightOneSpectrum (𝓞 K))) (N : ℕ) :
    Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S) :=
  Langlands.GaloisCohomology.rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) N

/-- `μ_N` is a smooth module of `G_S`. -/
instance isSmoothRep_dualizingModule (S : Set (HeightOneSpectrum (𝓞 K))) (N : ℕ) :
    IsSmoothRep (dualizingModule K Ω S N) :=
  isSmoothRep_rootsOfUnityModule N

omit [NumberField K] [IsGalois K Ω] in
/-- `μ_N` is killed by `N`. -/
theorem nsmul_dualizingModule (S : Set (HeightOneSpectrum (𝓞 K))) (N : ℕ)
    (ζ : dualizingModule K Ω S N) : N • ζ = 0 :=
  nsmul_rootsOfUnityModule_eq_zero N ζ

end Families

section LocalMaps

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) (N : ℕ)

/-- `μ_N` as a module of the local Galois group at a finite place is smooth. -/
instance isSmoothRep_localModule_dualizingModule (v : HeightOneSpectrum (𝓞 K)) :
    IsSmoothRep (localModule ι (dualizingModule K Ω S N) v) :=
  isSmoothRep_res _ _

/-- `μ_N` as a module of the local Galois group at an infinite place is smooth. -/
instance isSmoothRep_realLocalModule_dualizingModule (w : InfinitePlace K) :
    IsSmoothRep (realLocalModule ι (dualizingModule K Ω S N) w) :=
  isSmoothRep_res _ _

/-- The coefficient map `μ_N(K_S) → K̄_vˣ` of `ι` at a finite place `v`, a morphism of modules of
`G_{K_v}`. -/
def rootsOfUnityLocalHom (v : HeightOneSpectrum (𝓞 K)) :
    localModule ι (dualizingModule K Ω S N) v ⟶
      unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) :=
  Rep.ofHom ⟨(uliftIntLinearMap (MonoidHom.toAdditive
      ((Units.map (((ι.finite v).comp (maximalUnramifiedOutside K Ω S).val :
        maximalUnramifiedOutside K Ω S →ₐ[K] AlgebraicClosure (v.adicCompletion K)) :
          maximalUnramifiedOutside K Ω S →* AlgebraicClosure (v.adicCompletion K))).comp
        (rootsOfUnity N (maximalUnramifiedOutside K Ω S)).subtype)) :
      Additive (rootsOfUnity N (maximalUnramifiedOutside K Ω S)) →ₗ[ULift.{u} ℤ]
        Additive (AlgebraicClosure (v.adicCompletion K))ˣ), fun σ => by
    ext x
    exact Units.ext (localizationHom_apply ι S v σ
      (((Additive.toMul (show Additive (rootsOfUnity N (maximalUnramifiedOutside K Ω S)) from x) :
        rootsOfUnity N (maximalUnramifiedOutside K Ω S)) : (maximalUnramifiedOutside K Ω S)ˣ) :
          maximalUnramifiedOutside K Ω S))⟩

/-- `rootsOfUnityLocalHom` is `ι.finite v` on roots of unity. -/
theorem rootsOfUnityLocalHom_hom_apply (v : HeightOneSpectrum (𝓞 K))
    (x : Additive (rootsOfUnity N (maximalUnramifiedOutside K Ω S))) :
    (((Additive.toMul ((rootsOfUnityLocalHom ι S N v).hom x) :
        (AlgebraicClosure (v.adicCompletion K))ˣ)) : AlgebraicClosure (v.adicCompletion K)) =
      ι.finite v ((((Additive.toMul x : rootsOfUnity N (maximalUnramifiedOutside K Ω S)) :
        (maximalUnramifiedOutside K Ω S)ˣ) : maximalUnramifiedOutside K Ω S) : Ω) :=
  rfl

/-- The coefficient map `μ_N(K_S) → K̄_wˣ` of `ι` at an infinite place `w`. -/
def rootsOfUnityRealHom (w : InfinitePlace K) :
    realLocalModule ι (dualizingModule K Ω S N) w ⟶
      unitsModule w.Completion (AlgebraicClosure w.Completion) :=
  Rep.ofHom ⟨(uliftIntLinearMap (MonoidHom.toAdditive
      ((Units.map (((ι.infinite w).comp (maximalUnramifiedOutside K Ω S).val :
        maximalUnramifiedOutside K Ω S →ₐ[K] AlgebraicClosure w.Completion) :
          maximalUnramifiedOutside K Ω S →* AlgebraicClosure w.Completion)).comp
        (rootsOfUnity N (maximalUnramifiedOutside K Ω S)).subtype)) :
      Additive (rootsOfUnity N (maximalUnramifiedOutside K Ω S)) →ₗ[ULift.{u} ℤ]
        Additive (AlgebraicClosure w.Completion)ˣ), fun σ => by
    ext x
    exact Units.ext (realLocalizationHom_apply ι S w σ
      (((Additive.toMul (show Additive (rootsOfUnity N (maximalUnramifiedOutside K Ω S)) from x) :
        rootsOfUnity N (maximalUnramifiedOutside K Ω S)) : (maximalUnramifiedOutside K Ω S)ˣ) :
          maximalUnramifiedOutside K Ω S))⟩

/-- `rootsOfUnityRealHom` is `ι.infinite w` on roots of unity. -/
theorem rootsOfUnityRealHom_hom_apply (w : InfinitePlace K)
    (x : Additive (rootsOfUnity N (maximalUnramifiedOutside K Ω S))) :
    (((Additive.toMul ((rootsOfUnityRealHom ι S N w).hom x) :
        (AlgebraicClosure w.Completion)ˣ)) : AlgebraicClosure w.Completion) =
      ι.infinite w ((((Additive.toMul x : rootsOfUnity N (maximalUnramifiedOutside K Ω S)) :
        (maximalUnramifiedOutside K Ω S)ˣ) : maximalUnramifiedOutside K Ω S) : Ω) :=
  rfl

/-- The local invariant `H²(K_v, μ_N) → ℚ/ℤ` at a finite place: the class in `H²(K_v, K̄_vˣ)` followed
by the invariant of local class field theory (`finiteInvariant`). -/
def invariantAt (v : HeightOneSpectrum (𝓞 K)) :
    cohomology (localModule ι (dualizingModule K Ω S N) v) 2 →+ QZ :=
  QZ.toRationalModIntegers.symm.toAddMonoidHom.comp
    ((finiteInvariant v).toAddMonoidHom.comp
      (coeffMap (rootsOfUnityLocalHom ι S N v) 2).hom.toAddMonoidHom)

theorem invariantAt_apply (v : HeightOneSpectrum (𝓞 K))
    (x : cohomology (localModule ι (dualizingModule K Ω S N) v) 2) :
    invariantAt ι S N v x = QZ.toRationalModIntegers.symm
      (finiteInvariant v ((coeffMap (rootsOfUnityLocalHom ι S N v) 2).hom x)) :=
  rfl

/-- The local invariant `H²(K_w, μ_N) → ℚ/ℤ` at an infinite place: the class in `H²(K_w, K̄_wˣ)`
followed by the real invariant of the Brauer sequence (`realInvariantQZ`). -/
def realInvariantAt (w : InfinitePlace K) :
    cohomology (realLocalModule ι (dualizingModule K Ω S N) w) 2 →+ QZ :=
  (realInvariantQZ w).comp (coeffMap (rootsOfUnityRealHom ι S N w) 2).hom.toAddMonoidHom

theorem realInvariantAt_apply (w : InfinitePlace K)
    (x : cohomology (realLocalModule ι (dualizingModule K Ω S N) w) 2) :
    realInvariantAt ι S N w x = QZ.toRationalModIntegers.symm
      (realInvariant w ((coeffMap (rootsOfUnityRealHom ι S N w) 2).hom x)) :=
  rfl

end LocalMaps

section Reciprocity

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) (N : ℕ)

variable (Ω) in
/-- The image of a class of `H²(G_S, μ_N)` in the Brauer group `H²(Gal(Ω/K), Ωˣ)` of `K`. -/
def brauerClass : cohomology (dualizingModule K Ω S N) 2 →+ cohomology (unitsModule K Ω) 2 :=
  (maximalUnitsInflation K Ω S 2).comp
    (coeffMap (rootsOfUnityToUnits K (maximalUnramifiedOutside K Ω S) N) 2).hom.toAddMonoidHom

theorem brauerClass_apply (x : cohomology (dualizingModule K Ω S N) 2) :
    brauerClass Ω S N x = maximalUnitsInflation K Ω S 2
      ((coeffMap (rootsOfUnityToUnits K (maximalUnramifiedOutside K Ω S) N) 2).hom x) :=
  rfl

/-- `brauerClass` factors through the `S`-units. -/
theorem brauerClass_eq_maximalSUnitsInflation [NeZero N] (x : cohomology (dualizingModule K Ω S N) 2) :
    brauerClass Ω S N x = maximalSUnitsInflation K Ω S 2
      ((coeffMap (rootsOfUnityToSUnits S (maximalUnramifiedOutside K Ω S) N) 2).hom x) := by
  rw [brauerClass_apply, maximalSUnitsInflation_apply, ← ModuleCat.comp_apply, ← coeffMap_comp]
  rfl

/-- At a finite place, the Brauer class of `x` localizes to the image of the localization of `x`. -/
theorem brauerLocalization_brauerClass (v : HeightOneSpectrum (𝓞 K))
    (x : cohomology (dualizingModule K Ω S N) 2) :
    brauerLocalization ι v 2 (brauerClass Ω S N x) =
      (coeffMap (rootsOfUnityLocalHom ι S N v) 2).hom
        (localization ι (dualizingModule K Ω S N) v 2 x) := by
  rw [brauerClass_apply, maximalUnitsInflation_apply, brauerLocalization, LinearMap.toAddMonoidHom_coe,
    map_coeffMap_hom_apply, map_map_apply, localization_apply, ← ModuleCat.comp_apply,
    map_comp_coeffMap, Category.id_comp]
  have hφ : (GaloisGroupUnramifiedOutside.quotientMap K Ω S).comp
      (decompositionHom (v.adicCompletion K) (ι.finite v)) = localizationHom ι S v :=
    ContinuousMonoidHom.ext fun σ => (localizationHom_eq_quotientMap ι S v σ).symm
  rw [map_congr _ (rootsOfUnityLocalHom ι S N v) hφ ?_ 2]
  intro a
  rfl

/-- At an infinite place, the Brauer class of `x` localizes to the image of the localization of
`x`. -/
theorem realBrauerLocalization_brauerClass (w : InfinitePlace K)
    (x : cohomology (dualizingModule K Ω S N) 2) :
    realBrauerLocalization ι w 2 (brauerClass Ω S N x) =
      (coeffMap (rootsOfUnityRealHom ι S N w) 2).hom
        (realLocalization ι (dualizingModule K Ω S N) w 2 x) := by
  rw [brauerClass_apply, maximalUnitsInflation_apply, realBrauerLocalization, LinearMap.toAddMonoidHom_coe,
    map_coeffMap_hom_apply, map_map_apply, realLocalization_apply, ← ModuleCat.comp_apply,
    map_comp_coeffMap, Category.id_comp]
  have hφ : (GaloisGroupUnramifiedOutside.quotientMap K Ω S).comp
      (decompositionHom w.Completion (ι.infinite w)) = realLocalizationHom ι S w :=
    ContinuousMonoidHom.ext fun σ => (realLocalizationHom_eq_quotientMap ι S w σ).symm
  rw [map_congr _ (rootsOfUnityRealHom ι S N w) hφ ?_ 2]
  intro a
  rfl

/-- Outside `S` the Brauer class of a class of `H²(G_S, μ_N)` is locally trivial. -/
theorem brauerLocalization_brauerClass_eq_zero [NeZero N] {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S)
    (x : cohomology (dualizingModule K Ω S N) 2) :
    brauerLocalization ι v 2 (brauerClass Ω S N x) = 0 := by
  rw [brauerClass_eq_maximalSUnitsInflation]
  exact brauerLocalization_maximalSUnitsInflation_eq_zero S ι hv _

/-- The local invariant of the localization of `x` is the local invariant of its Brauer class. -/
theorem invariantAt_localization (v : HeightOneSpectrum (𝓞 K))
    (x : cohomology (dualizingModule K Ω S N) 2) :
    invariantAt ι S N v (localization ι (dualizingModule K Ω S N) v 2 x) =
      QZ.toRationalModIntegers.symm (localInvariant ι v (brauerClass Ω S N x)) := by
  rw [invariantAt_apply, localInvariant_apply, brauerLocalization_brauerClass]

/-- The real invariant of the localization of `x` is the real invariant of its Brauer class. -/
theorem realInvariantAt_realLocalization (w : InfinitePlace K)
    (x : cohomology (dualizingModule K Ω S N) 2) :
    realInvariantAt ι S N w (realLocalization ι (dualizingModule K Ω S N) w 2 x) =
      QZ.toRationalModIntegers.symm (realLocalInvariant ι w (brauerClass Ω S N x)) := by
  rw [realInvariantAt_apply, realLocalInvariant, realBrauerLocalization_brauerClass]

/-- **Reciprocity for `μ_N`.** The local invariants of the localizations of a class of
`H²(G_S, μ_N)` at the places of `S` and at the real places add up to zero. -/
theorem sum_invariantAt_add_sum_realInvariantAt [NeZero N] [Fintype S]
    (x : cohomology (dualizingModule K Ω S N) 2) :
    ∑ v : S, invariantAt ι S N v (localization ι (dualizingModule K Ω S N) v 2 x) +
      ∑ w : {w : InfinitePlace K // w.IsReal},
        realInvariantAt ι S N w (realLocalization ι (dualizingModule K Ω S N) w 2 x) = 0 := by
  classical
  have hsum := (localInvariant_finite_support_and_sum_eq_zero ι (brauerClass Ω S N x)).2
  have hfin : ∑ᶠ v, localInvariant ι v (brauerClass Ω S N x) =
      ∑ v : S, localInvariant ι v (brauerClass Ω S N x) := by
    have hsupp : Function.support (fun v => localInvariant ι v (brauerClass Ω S N x)) ⊆ S :=
      fun v hv => by
        by_contra hvS
        exact hv ((localInvariant_eq_zero_iff ι v _).2 (brauerLocalization_brauerClass_eq_zero ι S N hvS x))
    rw [finsum_eq_sum_of_support_subset _ (s := S.toFinset) (by simpa using hsupp)]
    exact (Finset.sum_subtype S.toFinset (fun a => by simp) _).trans rfl
  have hreal : ∑ w, realLocalInvariant ι w (brauerClass Ω S N x) =
      ∑ w : {w : InfinitePlace K // w.IsReal}, realLocalInvariant ι w.1 (brauerClass Ω S N x) := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun w : InfinitePlace K => w.IsReal)
      (fun w => by simp) (fun w => realLocalInvariant ι w (brauerClass Ω S N x)),
      Finset.sum_filter_of_ne]
    intro w _ hw
    by_contra hr
    have := subsingleton_realBrauerGroup_of_isComplex w (InfinitePlace.not_isReal_iff_isComplex.1 hr)
    exact hw ((realLocalInvariant_eq_zero_iff ι w _).2 (Subsingleton.elim _ _))
  rw [hfin, hreal] at hsum
  simp only [invariantAt_localization, realInvariantAt_realLocalization, ← map_sum, ← map_add, hsum,
    map_zero]

end Reciprocity

section Trace

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (N : ℕ) [NeZero N]

/-- The sum of the local invariants on `∏_{v ∈ S} H²(K_v, μ_N) × ∏_{w real} H²(K_w, μ_N)`. -/
def sumInvariants :
    ptTLocal (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N) 2 →+ QZ :=
  letI : Fintype S := Fintype.ofFinite S
  { toFun := fun ξ => ∑ v : S, invariantAt ι S N v (ξ.1 v) +
      ∑ w : {w : InfinitePlace K // w.IsReal}, realInvariantAt ι S N w (ξ.2 w)
    map_zero' := by
      simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, map_zero, Finset.sum_const_zero,
        add_zero]
    map_add' := fun ξ η => by
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, Finset.sum_add_distrib]
      abel }

omit [NeZero N] in
theorem sumInvariants_apply
    (ξ : ptTLocal (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N) 2) :
    sumInvariants ι S N ξ = letI : Fintype S := Fintype.ofFinite S
      ∑ v : S, invariantAt ι S N v (ξ.1 v) +
        ∑ w : {w : InfinitePlace K // w.IsReal}, realInvariantAt ι S N w (ξ.2 w) :=
  rfl

/-- The sum of the local invariants vanishes on the localizations of a global class. -/
theorem sumInvariants_globalToLocal (x : cohomology (dualizingModule K Ω S N) 2) :
    sumInvariants ι S N
      ((ptTGlobalToLocal (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N) 2).hom x) =
      0 := by
  let _ : Fintype S := Fintype.ofFinite S
  rw [sumInvariants_apply, ptTGlobalToLocal_apply]
  exact sum_invariantAt_add_sum_realInvariantAt ι S N x

/-- The sum of the local invariants vanishes on the kernel of
`∏ H²(·, μ_N) → Ĥ_c³(G_S, μ_N)`. -/
theorem ker_localToCompact_le_ker_sumInvariants :
    (ptTLocalToCompact (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N)
      2).hom.toAddMonoidHom.ker ≤ (sumInvariants ι S N).ker := by
  intro ξ hξ
  obtain ⟨x, rfl⟩ := (ptTExact_local (localFamily ι S) (realFamily ι S)
    (dualizingModule K Ω S N) 1 ξ).1 hξ
  exact sumInvariants_globalToLocal ι S N x

/-- The trace `Ĥ_c³(G_S, μ_N) → ℚ/ℤ`: an extension of the sum of the local invariants (a choice;
unique by `trace_localToCompact` once `∏ H²(·, μ_N) → Ĥ_c³` is known to be surjective). -/
def traceQZ :
    tateCompactCohomologyRes (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N) 3 →+ QZ :=
  (QZ.exists_comp_eq_of_ker_le _ _ (ker_localToCompact_le_ker_sumInvariants ι S N)).choose

theorem traceQZ_comp :
    (traceQZ ι S N).comp (ptTLocalToCompact (localFamily ι S) (realFamily ι S)
      (dualizingModule K Ω S N) 2).hom.toAddMonoidHom = sumInvariants ι S N :=
  (QZ.exists_comp_eq_of_ker_le _ _ (ker_localToCompact_le_ker_sumInvariants ι S N)).choose_spec

/-- The values of `traceQZ` are killed by `N`. -/
theorem nsmul_traceQZ
    (z : tateCompactCohomologyRes (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N) 3) :
    N • traceQZ ι S N z = 0 := by
  rw [← map_nsmul, nsmul_tateCompactCohomologyRes_eq_zero (localFamily ι S) (realFamily ι S)
    (nsmul_dualizingModule S N) 3 z, map_zero]

/-- **The trace** `Ĥ_c³(G_S, μ_N) → ℤ/N` of Poitou–Tate duality for `G_S`. -/
def trace :
    tateCompactCohomologyRes (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N) 3 →+
      ZMod N :=
  zmodOfQZ (traceQZ ι S N) (nsmul_traceQZ ι S N)

/-- On the image of the local terms, the trace is the sum of the local invariants. -/
theorem trace_localToCompact
    (ξ : ptTLocal (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N) 2) :
    zmodToQZ N (trace ι S N
      ((ptTLocalToCompact (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N) 2).hom ξ)) =
      sumInvariants ι S N ξ :=
  (zmodToQZ_zmodOfQZ _ _ _).trans (DFunLike.congr_fun (traceQZ_comp ι S N) ξ)

end Trace

end

end Langlands.GaloisCohomology.PoitouTate

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  PoitouTate

universe u

noncomputable section

section RootsOfUnityLocal

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} (ι : PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]

attribute [local instance 2000] IsSepClosure.isGalois

omit [NumberField K] [IsSepClosure K Ω] [NeZero N] in
/-- An element of `Additive Rˣ` killed by `N` is an `N`-th root of unity. -/
theorem toMul_mem_rootsOfUnity_of_nsmul {R : Type*} [CommMonoid R] (z : Additive Rˣ)
    (h : N • z = 0) : Additive.toMul z ∈ rootsOfUnity N R := by
  rw [mem_rootsOfUnity, ← toMul_nsmul, h]
  rfl

omit [NeZero N] in
/-- The local coefficient map `μ_N(K_S) → K̄_vˣ` is injective. -/
theorem rootsOfUnityLocalHom_injective (v : HeightOneSpectrum (𝓞 K)) :
    Function.Injective (rootsOfUnityLocalHom ι S N v).hom := by
  intro x y h
  have h' := congrArg (fun z : Additive (AlgebraicClosure (v.adicCompletion K))ˣ =>
    ((Additive.toMul z : (AlgebraicClosure (v.adicCompletion K))ˣ) :
      AlgebraicClosure (v.adicCompletion K))) h
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  exact (ι.finite v).toRingHom.injective h'

/-- Every `N`-th root of unity of `K̄_v` comes from `μ_N(K_S)`. -/
theorem exists_rootsOfUnityLocalHom_eq
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (v : HeightOneSpectrum (𝓞 K))
    (z : Additive (AlgebraicClosure (v.adicCompletion K))ˣ) (hz : N • z = 0) :
    ∃ x, (rootsOfUnityLocalHom ι S N v).hom x = z := by
  classical
  let F : rootsOfUnity N (maximalUnramifiedOutside K Ω S) →
      rootsOfUnity N (AlgebraicClosure (v.adicCompletion K)) := fun x =>
    ⟨Additive.toMul ((rootsOfUnityLocalHom ι S N v).hom
      (show localModule ι (dualizingModule K Ω S N) v from
        Additive.ofMul (α := rootsOfUnity N (maximalUnramifiedOutside K Ω S)) x)),
      toMul_mem_rootsOfUnity_of_nsmul N _ (by
        have h0 : N • (show localModule ι (dualizingModule K Ω S N) v from
            Additive.ofMul (α := rootsOfUnity N (maximalUnramifiedOutside K Ω S)) x) = 0 :=
          Local.nsmul_galRootsOfUnity_eq_zero (K := K) (Ksep := maximalUnramifiedOutside K Ω S) N _
        have h1 := map_nsmul (rootsOfUnityLocalHom ι S N v).hom N
          (show localModule ι (dualizingModule K Ω S N) v from
            Additive.ofMul (α := rootsOfUnity N (maximalUnramifiedOutside K Ω S)) x)
        rw [h0, map_zero] at h1
        exact h1.symm)⟩
  have hF : Function.Injective F := fun x y h => by
    have := rootsOfUnityLocalHom_injective ι N v (congrArg (fun z => Additive.ofMul z.1) h)
    exact Additive.ofMul.injective this
  have hKv : Nat.card (rootsOfUnity N (AlgebraicClosure (v.adicCompletion K))) = N :=
    HasEnoughRootsOfUnity.natCard_rootsOfUnity _ N
  have : Finite (rootsOfUnity N (AlgebraicClosure (v.adicCompletion K))) :=
    Nat.finite_of_card_ne_zero (by rw [hKv]; exact NeZero.ne N)
  have hFs : Function.Surjective F :=
    ((Function.Injective.bijective_of_nat_card_le hF
      (by rw [card_rootsOfUnity_maximalUnramifiedOutside N hS, hKv]))).2
  obtain ⟨x, hx⟩ := hFs ⟨_, toMul_mem_rootsOfUnity_of_nsmul N z hz⟩
  exact ⟨Additive.ofMul x, Additive.toMul.injective (congrArg Subtype.val hx)⟩

end RootsOfUnityLocal

section LocalKummer

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} (ι : PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)

attribute [local instance 2000] IsSepClosure.isGalois

variable (S) in
/-- The local Kummer sequence `0 → μ_N(K_S) → K̄_vˣ → K̄_vˣ → 0` of modules of `G_{K_v}`, with
`μ_N(K_S) → K̄_vˣ` given by `ι_v`. -/
def localKummerSequence (v : HeightOneSpectrum (𝓞 K)) :
    CategoryTheory.ShortComplex (Rep.{u} (ULift.{u} ℤ)
      Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)) :=
  CategoryTheory.ShortComplex.mk (rootsOfUnityLocalHom ι S N v)
    (N • 𝟙 (unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)))) (by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      change N • (rootsOfUnityLocalHom ι S N v).hom x = 0
      rw [← map_nsmul, Local.nsmul_galRootsOfUnity_eq_zero (K := K)
        (Ksep := maximalUnramifiedOutside K Ω S) N x, map_zero])

instance isSmoothRep_localKummerSequence_X₁ (v : HeightOneSpectrum (𝓞 K)) :
    IsSmoothRep (localKummerSequence S ι N v).X₁ :=
  inferInstanceAs (IsSmoothRep (localModule ι (dualizingModule K Ω S N) v))

instance isSmoothRep_localKummerSequence_X₂ (v : HeightOneSpectrum (𝓞 K)) :
    IsSmoothRep (localKummerSequence S ι N v).X₂ :=
  inferInstanceAs (IsSmoothRep (unitsModule (v.adicCompletion K)
    (AlgebraicClosure (v.adicCompletion K))))

instance isSmoothRep_localKummerSequence_X₃ (v : HeightOneSpectrum (𝓞 K)) :
    IsSmoothRep (localKummerSequence S ι N v).X₃ :=
  inferInstanceAs (IsSmoothRep (unitsModule (v.adicCompletion K)
    (AlgebraicClosure (v.adicCompletion K))))

include hS in
/-- The local Kummer sequence is short exact. -/
theorem localKummerSequence_shortExact (v : HeightOneSpectrum (𝓞 K)) :
    (localKummerSequence S ι N v).ShortExact where
  exact := shortComplex_exact_of_forall_exists _ fun z hz => by
    have hz' : N • z = 0 :=
      (nsmul_id_hom_apply (unitsModule (v.adicCompletion K)
        (AlgebraicClosure (v.adicCompletion K))) N z).symm.trans hz
    exact exists_rootsOfUnityLocalHom_eq ι N hS v z hz'
  mono_f := (Rep.mono_iff_injective _).2 (rootsOfUnityLocalHom_injective ι N v)
  epi_g := (Rep.epi_iff_surjective _).2 (nsmul_id_unitsModule_surjective N
    (Nat.cast_ne_zero.2 (NeZero.ne N)))

include hS in
/-- **Local Kummer theory in degree two.** `H²(K_v, μ_N) → H²(K_v, K̄_vˣ)` is injective. -/
theorem injective_coeffMap_rootsOfUnityLocalHom_two (v : HeightOneSpectrum (𝓞 K)) :
    Function.Injective (coeffMap (rootsOfUnityLocalHom ι S N v) 2).hom :=
  cohomologyMap_f_injective_of_subsingleton (localKummerSequence_shortExact ι N hS v) 1
    (subsingleton_cohomology_one_unitsModule (K := v.adicCompletion K)
      (L := AlgebraicClosure (v.adicCompletion K)))

end LocalKummer

end

end Langlands.GaloisCohomology
