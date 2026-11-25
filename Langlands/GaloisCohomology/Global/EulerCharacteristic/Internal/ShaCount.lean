import Langlands.GaloisCohomology.Global.EulerCharacteristic.ShaTwist
import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.KummerShaOpen
import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.Base

/-!
# The count of `Ш²` in Tate's base case

In the base case of Tate's computation (`L ⊆ K_S` Galois over `K` with group `Γ` of order prime to
the prime `ℓ`, `μ_ℓ ⊆ L`, `ℓ` odd or `L` totally complex, `M` killed by `ℓ` and trivial on
`P = G_S(L)`), `#Ш²_S(M) = ℓ^{d(A₁/ℓ)}` with `A₁ = H¹(P, 𝒪_Sˣ)` and `d(X) = dim (X ⊗ Hom(μ_ℓ, M))^Γ`
(`shaTwoBaseCount : ShaTwoBaseCountStatement`):

* `#Ш²_S(M) = ℓ^{dim Ш}` for the classes `Ш` of `H²(G_S, M)` over `𝔽_ℓ` vanishing at the places of
  `S` (`natCard_sha_two_eq_pow_finrank`; the real places impose nothing since `ℓ` is odd or `K` is
  totally complex);
* the Kummer map `A₁/ℓ → H²(P, μ_ℓ)` is injective and `Γ`-equivariant with image the classes
  vanishing on the Mackey family of `P` (`KummerShaOpen.lean`), so by the coprime twist
  (`finrank_shaSubmodule_eq_finrank_invariants`) `dim Ш = d(A₁/ℓ)`.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  Langlands.GaloisCohomology.Local Representation PoitouTate

universe u

noncomputable section

section Scalars

variable {k k' G : Type u} [CommRing k] [CommRing k'] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)]
  [∀ v, TopologicalSpace (Hv v)] [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
  {A : Rep.{u} k G} {A' : Rep.{u} k' G} [IsSmoothRep A] [IsSmoothRep A'] (e : A ≃+ A')
  (he : ∀ (g : G) (a : A), e (A.ρ g a) = A'.ρ g (e a))

/-- Vanishing on a family is preserved by a change of scalars of the coefficients. -/
theorem mem_shaSubmodule_cohomologyAddEquivOfEquiv_iff (n : ℕ) (x : cohomology A n) :
    cohomologyAddEquivOfEquiv e he n x ∈ shaSubmodule φ A' n ↔ x ∈ shaSubmodule φ A n := by
  refine forall_congr' fun v => ?_
  have key := cohomologyAddEquivOfEquiv_mapAlong e he (φ v)
    (B := Rep.res (φ v : Hv v →* G) A) (B' := Rep.res (φ v : Hv v →* G) A') e (fun _ a => he _ a)
    (𝟙 _) (𝟙 _) (fun _ => rfl) n x
  rw [← key]
  constructor
  · intro h
    exact (cohomologyAddEquivOfEquiv (A := Rep.res (φ v : Hv v →* G) A)
      (A' := Rep.res (φ v : Hv v →* G) A') e (fun _ a => he _ a) n).injective
      (h.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero]

end Scalars

section Base

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] {ℓ : ℕ} [Fact ℓ.Prime]
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
  (ι : PlaceEmbeddings K Ω)
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
  (hMℓ : ∀ m : M, ℓ • m = 0)

attribute [local instance 2000] IsSepClosure.isGalois

include hS in
/-- **The order of `Ш²`.** If the real places impose nothing (`ℓ` odd or `K` totally complex),
`#Ш²_S(M) = ℓ^{dim Ш}` for the classes `Ш` of `H²(G_S, M)` over `𝔽_ℓ` vanishing at the places of
`S`. -/
theorem natCard_sha_two_eq_pow_finrank (hK : Odd ℓ ∨ IsTotallyComplex K) :
    Nat.card (sha ι M 2) = ℓ ^ Module.finrank (ULift.{u} (ZMod ℓ))
      (shaSubmodule (localFamily ι S) (zmodRepOfTorsion ℓ M hMℓ) 2) := by
  have hSM := mem_of_natCard_mem_of_nsmul_eq_zero hS hMℓ
  have := finite_cohomology_of_le_two M hSM 2 le_rfl
  let E := cohomologyZModEquiv ℓ M hMℓ 2
  have hmem : ∀ x, x ∈ sha ι M 2 ↔ E x ∈ shaSubmodule (localFamily ι S)
      (zmodRepOfTorsion ℓ M hMℓ) 2 := fun x => by
    refine Iff.trans ?_ (mem_shaSubmodule_cohomologyAddEquivOfEquiv_iff (localFamily ι S)
      (zmodRepOfTorsionEquiv ℓ M hMℓ) (fun _ _ => rfl) 2 x).symm
    rw [mem_sha]
    constructor
    · rintro ⟨h, -⟩ v
      exact h v.1 v.2
    · intro h
      refine ⟨fun v hv => h ⟨v, hv⟩, fun w hw => ?_⟩
      rcases hK with ho | hc
      · exact eq_zero_cohomology_closureGalois_of_odd w hw _ ho (fun a => hMℓ a) (by norm_num) _
      · exact absurd hw (InfinitePlace.not_isReal_iff_isComplex.2 (hc.isComplex w))
  have : Finite (cohomology (zmodRepOfTorsion ℓ M hMℓ) 2) := Finite.of_equiv _ E.toEquiv
  have hc : Nat.card (sha ι M 2) = Nat.card (shaSubmodule (localFamily ι S)
      (zmodRepOfTorsion ℓ M hMℓ) 2) :=
    Nat.card_congr (E.toEquiv.subtypeEquiv hmem)
  rw [hc, natCard_eq_pow_finrank_zmod ℓ]

end Base

section Dimension

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] {ℓ : ℕ} [Fact ℓ.Prime]
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
  {L : Type u} [Field L] [NumberField L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) [IsGalois K L]
  [(GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal]
  (hcop : Nat.Coprime (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)).index ℓ)
  (hζ : ∃ ζ : L, IsPrimitiveRoot ζ ℓ) (ι : PlaceEmbeddings K Ω)
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
  (hMℓ : ∀ m : M, ℓ • m = 0)
  (hMP : ∀ g ∈ (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)), M.ρ g = 1)

attribute [local instance 2000] IsSepClosure.isGalois

/-- The Kummer map `A₁/ℓ → H²(P, μ_ℓ)` over `𝔽_ℓ`, `A₁ = H¹(P, 𝒪_Sˣ)`. -/
def kummerModNZMod :
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
    ModN (cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)) 1) ℓ →ₗ[
        ULift.{u} (ZMod ℓ)]
      cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (zmodRepOfTorsion ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
          (nsmul_galRootsOfUnity_eq_zero ℓ))) 2 :=
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  zmodLinearOfAddHom ℓ ((cohomologyAddEquivOfEquiv (A := Rep.res
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ))
      (A' := Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (zmodRepOfTorsion ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
          (nsmul_galRootsOfUnity_eq_zero ℓ)))
      (zmodRepOfTorsionEquiv ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
        (nsmul_galRootsOfUnity_eq_zero ℓ)) (fun _ _ => rfl)
        (1 + 1)).toAddMonoidHom.comp
    (kummerModNHom (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (baseKummer_shortExact (Ω := Ω) hS) 1))

omit [Finite S] [IsGalois K L] [(GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal] in
include hS in
/-- `kummerModNZMod` is `δ` followed by the change of scalars. -/
theorem kummerModNZMod_mk (y : cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S
    hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)) 1) :
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    kummerModNZMod hS hL (Submodule.Quotient.mk y) = cohomologyAddEquivOfEquiv (A := Rep.res
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ))
      (A' := Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (zmodRepOfTorsion ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
          (nsmul_galRootsOfUnity_eq_zero ℓ)))
      (zmodRepOfTorsionEquiv ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
        (nsmul_galRootsOfUnity_eq_zero ℓ)) (fun _ _ => rfl) (1 + 1)
      (kummerModNHom (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (baseKummer_shortExact (Ω := Ω) hS) 1
        (Submodule.Quotient.mk y)) :=
  rfl

omit [Finite S] [IsGalois K L] [(GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal] in
include hS in
/-- The Kummer map is injective. -/
theorem kummerModNZMod_injective :
    Function.Injective (kummerModNZMod hS hL) :=
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  (cohomologyAddEquivOfEquiv (A := Rep.res
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ))
      (A' := Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (zmodRepOfTorsion ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
          (nsmul_galRootsOfUnity_eq_zero ℓ)))
      (zmodRepOfTorsionEquiv ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
        (nsmul_galRootsOfUnity_eq_zero ℓ)) (fun _ _ => rfl) (1 + 1)).injective.comp
    (kummerModNHom_injective _ _ 1)

omit [Finite S] in
include hS in
/-- The Kummer map is `Γ`-equivariant. -/
theorem isIntertwiningMap_kummerModNZMod :
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    (letI := conjAction (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (quotientGalEquiv hL)
        (maximalSUnitsModule K Ω S) 1;
      Representation.IsIntertwiningMap ((zmodRepULift.{u} (modNRep (L ≃ₐ[K] L) (cohomology (Rep.res
        (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)) 1) ℓ)).comp
        (quotientGalEquiv hL).toMonoidHom)
      (cohomologyConjRep (zmodRepOfTorsion ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
        (nsmul_galRootsOfUnity_eq_zero ℓ)) (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)) 2) (kummerModNZMod hS hL)) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  let := conjAction (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (quotientGalEquiv hL) (maximalSUnitsModule K Ω S) 1
  refine ⟨fun q x => ?_⟩
  induction q using QuotientGroup.induction_on with
  | H g =>
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      have h1 : modNRep (L ≃ₐ[K] L) (cohomology (Rep.res
          (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
            Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)) 1) ℓ
          (quotientGalEquiv hL (g : _ ⧸ _)) (Submodule.Quotient.mk y) =
          Submodule.Quotient.mk ((cohomologyConj (maximalSUnitsModule K Ω S)
            (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
              Subgroup (GaloisGroupUnramifiedOutside K Ω S)) 1 g).hom y) := by
        rw [modNRep_mk, conjAction_smul]
      have h2 := kummerModNHom_cohomologyConj (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (baseKummer_shortExact (Ω := Ω) hS) 1 g y
      have h3 := cohomologyAddEquivOfEquiv_cohomologyConj (A := rootsOfUnityModule K
        (maximalUnramifiedOutside K Ω S) ℓ)
        (A' := zmodRepOfTorsion ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
          (nsmul_galRootsOfUnity_eq_zero ℓ))
        (zmodRepOfTorsionEquiv ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
          (nsmul_galRootsOfUnity_eq_zero ℓ)) (fun _ _ => rfl) _ (1 + 1) g
          (kummerModNHom (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
            Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (baseKummer_shortExact (Ω := Ω) hS) 1
            (Submodule.Quotient.mk y))
      refine (congrArg (kummerModNZMod hS hL) h1).trans ?_
      refine ((congrArg _ h2).trans h3).trans ?_
      rw [cohomologyConjRep_mk]
      rfl

omit [Finite S] [IsGalois K L] [(GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal] in
include hS in
/-- **The image of the Kummer map.** A class of `H²(P, μ_ℓ)` over `𝔽_ℓ` vanishes on the Mackey
family of `P` exactly when it comes from `A₁/ℓ`. -/
theorem mem_shaSubmodule_mackey_iff_mem_range_kummerModNZMod (hc : ℓ ≠ 2 ∨ IsTotallyComplex L)
    (y : cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (zmodRepOfTorsion ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
          (nsmul_galRootsOfUnity_eq_zero ℓ))) 2) :
    y ∈ shaSubmodule (mackeyFamily (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
        (localFamily ι S)) (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (zmodRepOfTorsion ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
          (nsmul_galRootsOfUnity_eq_zero ℓ))) 2 ↔
      y ∈ LinearMap.range (kummerModNZMod hS hL) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  let E := cohomologyAddEquivOfEquiv (A := Rep.res
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ))
      (A' := Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (zmodRepOfTorsion ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
          (nsmul_galRootsOfUnity_eq_zero ℓ)))
      (zmodRepOfTorsionEquiv ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
        (nsmul_galRootsOfUnity_eq_zero ℓ)) (fun _ _ => rfl) 2
  obtain ⟨y', rfl⟩ := E.surjective y
  refine (mem_shaSubmodule_cohomologyAddEquivOfEquiv_iff (mackeyFamily
    (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL) (localFamily ι S))
    (A := Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ))
    (A' := Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (zmodRepOfTorsion ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
          (nsmul_galRootsOfUnity_eq_zero ℓ)))
    (zmodRepOfTorsionEquiv ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
      (nsmul_galRootsOfUnity_eq_zero ℓ)) (fun _ _ => rfl) 2 y').trans ?_
  refine (mem_shaSubmodule_mackey_iff_coeffMap_eq_zero hL ℓ ι (Fact.out : ℓ.Prime) hS hc y').trans ?_
  have hk := kummerTorsHom_eq_zero_iff (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (baseKummer_shortExact (Ω := Ω) hS) 1 y'
  constructor
  · intro h
    obtain ⟨z, hz⟩ := hk.1 (Subtype.ext h)
    exact ⟨z, congrArg E hz⟩
  · rintro ⟨z, hz⟩
    have hz' := E.injective hz
    exact congrArg Subtype.val (hk.2 ⟨z, hz'⟩)

omit [Finite S] in
include hS in
/-- **The dimension of `Ш²`.** The classes of `H²(G_S, M)` over `𝔽_ℓ` vanishing at the places of
`S` have dimension `d(A₁/ℓ)` (`baseShaExponent`). -/
theorem finrank_shaSubmodule_two_eq_baseShaExponent (hc : ℓ ≠ 2 ∨ IsTotallyComplex L) :
    (Module.finrank (ULift.{u} (ZMod ℓ))
      (shaSubmodule (localFamily ι S) (zmodRepOfTorsion ℓ M hMℓ) 2) : ℤ) =
      baseShaExponent hL hcop hζ M hMℓ hMP := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have : Finite (zmodRepOfTorsion ℓ M hMℓ) := inferInstanceAs (Finite M)
  have : Module.Finite (ULift.{u} (ZMod ℓ)) (zmodRepOfTorsion ℓ M hMℓ) := Module.Finite.of_finite
  let := conjAction (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (quotientGalEquiv hL) (maximalSUnitsModule K Ω S) 1
  have hdim := finrank_shaSubmodule_eq_finrank_invariants (localFamily ι S)
    (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
    (zmodRepOfTorsion ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
      (nsmul_galRootsOfUnity_eq_zero ℓ)) (zmodRepOfTorsion ℓ M hMℓ)
    (rootsOfUnity_res_trivial hL hζ) (res_apply_eq_of_trivial hL M hMP)
    (finrank_zmodRepOfTorsion_rootsOfUnity hS) (index_ne_zero_zmod hL hcop) 2 _
    (kummerModNZMod hS hL) (isIntertwiningMap_kummerModNZMod hS hL) (kummerModNZMod_injective hS hL)
    (fun y => mem_shaSubmodule_mackey_iff_mem_range_kummerModNZMod hS hL ι hc y)
  rw [hdim]
  exact congrArg (fun n : ℕ => (n : ℤ)) (finrank_invariants_tprod_comp_mulEquiv _ _ _)

/-- **The count of `Ш²` in the base case.** -/
theorem shaTwoBaseCount : ShaTwoBaseCountStatement.{u} := by
  intro K Ω _ _ _ _ _ S _ ℓ _ hS L _ _ _ _ _ hL _ _ hcop hζ hc ι M _ _ hMℓ hMP
  exact ⟨_, natCard_sha_two_eq_pow_finrank hS ι M hMℓ (odd_or_isTotallyComplex hL hcop hc),
    finrank_shaSubmodule_two_eq_baseShaExponent hS hL hcop hζ ι M hMℓ hMP hc⟩

end Dimension

end

end Langlands.GaloisCohomology
