import Langlands.GaloisCohomology.Global.EulerCharacteristic.KummerSha
import Langlands.GaloisCohomology.Global.EulerCharacteristic.ShaDescent
import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.BaseKummer
import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.KummerCount

/-!
# `Ш²` of the roots of unity over an open subgroup of `G_S`

Let `L ⊆ K_S` be a finite extension of `K`, `P = G_S(L)` the open subgroup of `G_S` fixing `L`,
which is `G_{S_L}(L)` (`fixingOpenSubgroupEquiv`), and `μ_ℓ = μ_ℓ(K_S) = μ_ℓ(L_{S_L})`. The localization
of `P` is the Mackey family of the localization of `G_S` (`mackeyFamily P (localFamily ι S)`): its local
groups are the decomposition groups of the places of `L` above `S` (`mackeyPlaceEquiv`,
`mackeyLocalEquiv`), up to conjugation in `G_{S_L}(L)`
(`exists_fixingOpenSubgroupEquiv_mackeyConj_eq_localizationHom`). Transporting along these
identifications (`resRootsOfUnityHom`, `resMaximalSUnitsHom`):

* a class of `Hⁿ(P, μ_ℓ)` vanishes on the Mackey family exactly when its image in
  `Hⁿ(G_{S_L}(L), μ_ℓ)` vanishes at the places of `L` above `S`
  (`map_mackeyFamily_eq_zero_iff_localization`);
* for `n = 2`, `ℓ` prime and `ℓ` odd or `L` totally complex, this happens exactly when the class
  is the image of `H¹(P, 𝒪_Sˣ)` under the Kummer connecting map
  (`mem_shaSubmodule_mackey_iff_exists_kummerModNHom`), by `Ш²_{S_L}(L, μ_ℓ)` of `KummerSha.lean`.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  PoitouTate
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

universe u

noncomputable section

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} {L : Type u} [Field L] [NumberField L] [Algebra K L]
  [Algebra L Ω] [IsScalarTower K L Ω]
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) (N : ℕ)

attribute [local instance 2000] IsSepClosure.isGalois

section Transport

/-- The isomorphism `P ≅ G_{S_L}(L)` read backwards, as a continuous homomorphism. -/
abbrev fixingOpenSubgroupEquivSymm :
    GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S) →ₜ*
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)) :=
  ⟨(GaloisGroupUnramifiedOutside.fixingOpenSubgroupEquiv S hL).symm.toMulEquiv.toMonoidHom,
    (GaloisGroupUnramifiedOutside.fixingOpenSubgroupEquiv S hL).symm.continuous⟩

/-- `μ_N(K_S)` restricted to `P ≅ G_{S_L}(L)` is `μ_N(L_{S_L})`. -/
def resRootsOfUnityHom :
    Rep.res (fixingOpenSubgroupEquivSymm hL : GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S) →*
        (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)))
      (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (dualizingModule K Ω S N)) ⟶
      dualizingModule L Ω (finitePlacesAbove L S) N :=
  Rep.ofHom ⟨(uliftIntLinearEquivAddHom _ _).symm
    { toFun := fun x => Additive.ofMul (restrictRootsOfUnity (maximalUnramifiedOutsideEquiv hL :
          maximalUnramifiedOutside K Ω S →* maximalUnramifiedOutside L Ω (finitePlacesAbove L S)) N
          (Additive.toMul (α := rootsOfUnity N (maximalUnramifiedOutside K Ω S)) x))
      map_zero' := by rw [toMul_zero, map_one, ofMul_one]
      map_add' := fun x y => by rw [toMul_add, map_mul, ofMul_mul] },
    fun τ => LinearMap.ext fun x => by
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Units.ext
      apply Subtype.ext
      exact (GaloisGroupUnramifiedOutside.coe_fixingOpenSubgroupEquiv_symm_apply hL τ _)⟩

/-- `resRootsOfUnityHom` is `K_S ≅ L_{S_L}` on roots of unity. -/
theorem resRootsOfUnityHom_hom_apply (x : dualizingModule K Ω S N) :
    (resRootsOfUnityHom hL N).hom x = Additive.ofMul (restrictRootsOfUnity
      (maximalUnramifiedOutsideEquiv hL :
        maximalUnramifiedOutside K Ω S →* maximalUnramifiedOutside L Ω (finitePlacesAbove L S)) N
      (Additive.toMul (α := rootsOfUnity N (maximalUnramifiedOutside K Ω S)) x)) :=
  rfl

theorem resRootsOfUnityHom_bijective : Function.Bijective (resRootsOfUnityHom hL N).hom := by
  constructor
  · intro x y h
    rw [resRootsOfUnityHom_hom_apply, resRootsOfUnityHom_hom_apply] at h
    have h' := congrArg (fun z : Additive (rootsOfUnity N
      (maximalUnramifiedOutside L Ω (finitePlacesAbove L S))) =>
        (((Additive.toMul z : rootsOfUnity N _) : (maximalUnramifiedOutside L Ω
          (finitePlacesAbove L S))ˣ) : maximalUnramifiedOutside L Ω (finitePlacesAbove L S))) h
    exact Additive.toMul.injective (Subtype.ext (Units.ext
      ((maximalUnramifiedOutsideEquiv hL).injective h')))
  · intro y
    refine ⟨Additive.ofMul (restrictRootsOfUnity ((maximalUnramifiedOutsideEquiv hL).symm :
      maximalUnramifiedOutside L Ω (finitePlacesAbove L S) →* maximalUnramifiedOutside K Ω S) N
        (Additive.toMul y)), (resRootsOfUnityHom_hom_apply hL N _).trans ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    exact (maximalUnramifiedOutsideEquiv hL).apply_symm_apply _

variable [NeZero N]

/-- The transport of the roots of unity commutes with the inclusions into the `S`-units. -/
theorem resRootsOfUnityHom_comp_rootsOfUnityToSUnits :
    resRootsOfUnityHom hL N ≫ rootsOfUnityToSUnits (finitePlacesAbove L S)
        (maximalUnramifiedOutside L Ω (finitePlacesAbove L S)) N =
      (Rep.resFunctor (fixingOpenSubgroupEquivSymm hL :
          GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S) →*
            (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
              Subgroup (GaloisGroupUnramifiedOutside K Ω S)))).map
        ((Rep.resFunctor (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype).map
          (rootsOfUnityToSUnits S (maximalUnramifiedOutside K Ω S) N)) ≫ resMaximalSUnitsHom hL :=
  Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))

end Transport

section Open

variable (ι : PlaceEmbeddings K Ω) (ιL : PlaceEmbeddings L Ω) [NeZero N] [IsGalois L Ω]

/-- The transport of a class of `Hⁿ(P, μ_N)` to `Hⁿ(G_{S_L}(L), μ_N)`. -/
abbrev rootsOfUnityTransport (n : ℕ) :
    cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (dualizingModule K Ω S N)) n ⟶
      cohomology (dualizingModule L Ω (finitePlacesAbove L S) N) n :=
  map (fixingOpenSubgroupEquivSymm hL) (resRootsOfUnityHom hL N) n

/-- The transport commutes with the Kummer maps into the `S`-units. -/
theorem coeffMap_rootsOfUnityTransport (n : ℕ)
    (y : cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (dualizingModule K Ω S N)) n) :
    (coeffMap (rootsOfUnityToSUnits (finitePlacesAbove L S)
        (maximalUnramifiedOutside L Ω (finitePlacesAbove L S)) N) n).hom
        ((rootsOfUnityTransport hL N n).hom y) =
      (map (fixingOpenSubgroupEquivSymm hL) (resMaximalSUnitsHom hL) n).hom
        ((coeffMap ((Rep.resFunctor (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype).map
            (rootsOfUnityToSUnits S (maximalUnramifiedOutside K Ω S) N)) n).hom y) := by
  rw [← ModuleCat.comp_apply, map_comp_coeffMap, resRootsOfUnityHom_comp_rootsOfUnityToSUnits,
    map_coeffMap_hom_apply]

/-- The transport of the `S`-units is injective on cohomology. -/
theorem injective_map_resMaximalSUnitsHom (n : ℕ) :
    Function.Injective (map (fixingOpenSubgroupEquivSymm hL) (resMaximalSUnitsHom hL) n).hom := by
  let e := GaloisGroupUnramifiedOutside.fixingOpenSubgroupEquiv S hL
  have hiso := isIso_map_of_mulEquiv e.symm.toMulEquiv e.symm.continuous e.continuous
    (resMaximalSUnitsHom hL) (resMaximalSUnitsHom_bijective hL) n
  exact (ModuleCat.mono_iff_injective _).1 inferInstance

omit [NeZero N] in
/-- The transport of the roots of unity is bijective on cohomology. -/
theorem bijective_rootsOfUnityTransport (n : ℕ) :
    Function.Bijective (rootsOfUnityTransport hL N n).hom := by
  let e := GaloisGroupUnramifiedOutside.fixingOpenSubgroupEquiv S hL
  have hiso := isIso_map_of_mulEquiv e.symm.toMulEquiv e.symm.continuous e.continuous
    (resRootsOfUnityHom hL N) (resRootsOfUnityHom_bijective hL N) n
  have : IsIso (rootsOfUnityTransport hL N n) := hiso
  exact ConcreteCategory.bijective_of_isIso _

/-- `μ_N` restricted to a local group of the Mackey family of `P` is smooth. -/
instance isSmoothRep_res_mackeyFamily_dualizingModule
    (p : MackeyIndex (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL) (localFamily ι S)) :
    IsSmoothRep (Rep.res (mackeyFamily (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
      (localFamily ι S) p : mackeyGroup (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
        (localFamily ι S) p →* (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)))
      (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (dualizingModule K Ω S N))) :=
  isSmoothRep_res _ _

/-- Conjugation by `g` after the decomposition homomorphism at `w`. -/
abbrev conjLocalizationHom (ιL : PlaceEmbeddings L Ω) (w : HeightOneSpectrum (𝓞 L))
    (g : GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S)) :
    Gal(AlgebraicClosure (w.adicCompletion L)/w.adicCompletion L) →ₜ*
      GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S) :=
  (⟨innerConjHom g, continuous_innerConjHom g⟩ :
    GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S) →ₜ*
      GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S)).comp
    (localizationHom ιL (finitePlacesAbove L S) w)

/-- `μ_N(K_S)` restricted to `P` and transported to `G_{S_L}(L)`. -/
abbrev transportModule : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S)) :=
  Rep.res (fixingOpenSubgroupEquivSymm hL : GaloisGroupUnramifiedOutside L Ω
    (finitePlacesAbove L S) →* (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S))) (Rep.res
        (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (dualizingModule K Ω S N))

instance isSmoothRep_transportModule : IsSmoothRep (transportModule hL N) :=
  isSmoothRep_res _ _

omit [NeZero N] in
/-- Restriction of a class of `Hⁿ(P, μ_N)` along `φ' = (P ≅ G_{S_L}(L)) ∘ (conjugate of the
decomposition homomorphism at w) ∘ m`, `m` an isomorphism, vanishes exactly when the localization
at `w` of its transport vanishes. -/
theorem map_eq_zero_iff_localization_of_comp (n : ℕ) {H : Type u} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (w : HeightOneSpectrum (𝓞 L))
    (m : H ≃ₜ* Gal(AlgebraicClosure (w.adicCompletion L)/w.adicCompletion L))
    (g : GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S))
    (φ' : H →ₜ* (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)))
    (hφ' : (fixingOpenSubgroupEquivSymm hL).comp
      ((conjLocalizationHom ιL w g).comp (m : H →ₜ* _)) = φ')
    (y : cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (dualizingModule K Ω S N)) n)
    [hR : IsSmoothRep (Rep.res (φ' : H →* (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S))) (Rep.res
        (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (dualizingModule K Ω S N)))] :
    (map φ' (𝟙 _) n).hom y = 0 ↔
      localization ιL (dualizingModule L Ω (finitePlacesAbove L S) N) w n
        ((rootsOfUnityTransport hL N n).hom y) = 0 := by
  subst hφ'
  have : IsSmoothRep (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (dualizingModule K Ω S N)) :=
    isSmoothRep_res_subtype _ _
  have := isSmoothRep_res (fixingOpenSubgroupEquivSymm hL) (Rep.res
    (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (dualizingModule K Ω S N))
  have := isSmoothRep_res (conjLocalizationHom ιL w g) (transportModule hL N)
  have := isSmoothRep_res (localizationHom ιL (finitePlacesAbove L S) w) (transportModule hL N)
  have := isSmoothRep_res (m : H →ₜ* _) (Rep.res (conjLocalizationHom ιL w g :
    Gal(AlgebraicClosure (w.adicCompletion L)/w.adicCompletion L) →*
      GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S)) (transportModule hL N))
  have h1 := map_map_apply (fixingOpenSubgroupEquivSymm hL) (𝟙 _) (conjLocalizationHom ιL w g)
    (𝟙 _) n y
  have h1' := map_map_apply ((fixingOpenSubgroupEquivSymm hL).comp (conjLocalizationHom ιL w g))
    ((Rep.resFunctor (conjLocalizationHom ιL w g : Gal(AlgebraicClosure (w.adicCompletion L)/
      w.adicCompletion L) →* GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S))).map (𝟙 (transportModule hL N)) ≫
        𝟙 _) (m : H →ₜ* _) (𝟙 _) n y
  have hc : (map ((fixingOpenSubgroupEquivSymm hL).comp
      ((conjLocalizationHom ιL w g).comp (m : H →ₜ* _))) (𝟙 _) n).hom y =
      (map (m : H →ₜ* _) (𝟙 _) n).hom ((map (conjLocalizationHom ιL w g) (𝟙 _) n).hom
        ((map (fixingOpenSubgroupEquivSymm hL) (𝟙 (transportModule hL N)) n).hom y)) := by
    rw [h1, h1']
    exact congrArg (fun F => F.hom y) (ProfiniteCohomology.map_congr (A := Rep.res
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (dualizingModule K Ω S N))
      (B := Rep.res ((m : H →ₜ* Gal(AlgebraicClosure (w.adicCompletion L)/w.adicCompletion L)) :
        H →* Gal(AlgebraicClosure (w.adicCompletion L)/w.adicCompletion L))
        (Rep.res (conjLocalizationHom ιL w g :
        Gal(AlgebraicClosure (w.adicCompletion L)/w.adicCompletion L) →*
          GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S)) (transportModule hL N))) _ _ rfl (fun _ => rfl) n)
  have h2 : (rootsOfUnityTransport hL N n).hom y = (coeffMap (resRootsOfUnityHom hL N) n).hom
      ((map (fixingOpenSubgroupEquivSymm hL) (𝟙 (transportModule hL N)) n).hom y) := by
    change _ = (map (fixingOpenSubgroupEquivSymm hL) (𝟙 (transportModule hL N)) n ≫
      coeffMap (resRootsOfUnityHom hL N) n).hom y
    rw [map_comp_coeffMap, Category.id_comp]
  set z := (map (fixingOpenSubgroupEquivSymm hL) (𝟙 (transportModule hL N)) n).hom y with hz
  have h3 : localization ιL (dualizingModule L Ω (finitePlacesAbove L S) N) w n
      ((coeffMap (resRootsOfUnityHom hL N) n).hom z) =
      (coeffMap ((Rep.resFunctor (localizationHom ιL (finitePlacesAbove L S) w :
        Gal(AlgebraicClosure (w.adicCompletion L)/w.adicCompletion L) →*
          GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S))).map
            (resRootsOfUnityHom hL N)) n).hom
        ((map (localizationHom ιL (finitePlacesAbove L S) w) (𝟙 _) n).hom z) := by
    refine (map_coeffMap_hom_apply (localizationHom ιL (finitePlacesAbove L S) w)
      (resRootsOfUnityHom hL N) (𝟙 _) n z).trans ?_
    refine (congrArg (fun F => F.hom z) (ProfiniteCohomology.map_congr (A := transportModule hL N)
      (B := localModule ιL (dualizingModule L Ω (finitePlacesAbove L S) N) w) _
      (𝟙 _ ≫ (Rep.resFunctor (localizationHom ιL (finitePlacesAbove L S) w :
        Gal(AlgebraicClosure (w.adicCompletion L)/w.adicCompletion L) →*
          GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S))).map
            (resRootsOfUnityHom hL N)) rfl (fun _ => rfl) n)).trans ?_
    exact (congrArg (fun F => F.hom z) (map_comp_coeffMap (transportModule hL N)
      (localizationHom ιL (finitePlacesAbove L S) w) (𝟙 _) ((Rep.resFunctor
        (localizationHom ιL (finitePlacesAbove L S) w : Gal(AlgebraicClosure (w.adicCompletion L)/
          w.adicCompletion L) →* GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S))).map
            (resRootsOfUnityHom hL N)) n)).symm
  have hR := (congrArg (localization ιL (dualizingModule L Ω (finitePlacesAbove L S) N) w n) h2).trans h3
  constructor
  · intro h
    have h' := injective_map_of_continuousMulEquiv m _ n ((hc.symm.trans h).trans (map_zero _).symm)
    rw [hR, (map_conj_apply_eq_zero_iff (transportModule hL N)
      (localizationHom ιL (finitePlacesAbove L S) w) (conjLocalizationHom ιL w g) g (fun _ => rfl)
        n z).1 h', map_zero]
  · intro h
    have h' := injective_coeffMap_of_bijective ((Rep.resFunctor
      (localizationHom ιL (finitePlacesAbove L S) w : Gal(AlgebraicClosure (w.adicCompletion L)/
        w.adicCompletion L) →* GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S))).map
          (resRootsOfUnityHom hL N)) (resRootsOfUnityHom_bijective hL N) n
      ((hR.symm.trans h).trans (map_zero _).symm)
    have h'' := (map_conj_apply_eq_zero_iff (transportModule hL N)
      (localizationHom ιL (finitePlacesAbove L S) w) (conjLocalizationHom ιL w g) g (fun _ => rfl)
        n z).2 h'
    exact hc.trans ((congrArg _ h'').trans (map_zero _))

omit [NeZero N] in
/-- **The local groups of `P`.** Restriction along the Mackey family at `p` vanishes on a class of
`Hⁿ(P, μ_N)` exactly when the localization at the place `w` of `L` attached to `p` vanishes on its
transport to `G_{S_L}(L)`. -/
theorem map_mackeyFamily_eq_zero_iff_localization (n : ℕ)
    (p : MackeyIndex (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL) (localFamily ι S))
    (y : cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (dualizingModule K Ω S N)) n) :
    (map (mackeyFamily (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL) (localFamily ι S) p)
        (𝟙 _) n).hom y = 0 ↔
      localization ιL (dualizingModule L Ω (finitePlacesAbove L S) N)
        (Langlands.Galois.localPlace hL ι p.1 p.2.out).1 n
          ((rootsOfUnityTransport hL N n).hom y) = 0 := by
  have hex := exists_fixingOpenSubgroupEquiv_mackeyConj_eq_localizationHom hL ι ιL
    (p.1 : HeightOneSpectrum (𝓞 K)) p.2.out
  refine hex.elim fun g hg => map_eq_zero_iff_localization_of_comp hL N ιL n _
    (mackeyLocalEquiv hL ι p.1 p.2.out) g _ ?_ y (hR := isSmoothRep_res _ _)
  refine ContinuousMonoidHom.ext fun σ => ?_
  exact (GaloisGroupUnramifiedOutside.fixingOpenSubgroupEquiv S hL).toMulEquiv.symm_apply_eq.2
    (hg σ).symm

omit [NeZero N] in
/-- A class of `Hⁿ(P, μ_N)` vanishes on the Mackey family of `P` exactly when its transport to
`G_{S_L}(L)` vanishes at every place of `L` above `S`. -/
theorem mem_shaSubmodule_mackey_iff (n : ℕ)
    (y : cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (dualizingModule K Ω S N)) n) :
    y ∈ shaSubmodule (mackeyFamily (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
        (localFamily ι S)) (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (dualizingModule K Ω S N)) n ↔
      ∀ w ∈ finitePlacesAbove L S, localization ιL (dualizingModule L Ω (finitePlacesAbove L S) N)
        w n ((rootsOfUnityTransport hL N n).hom y) = 0 := by
  constructor
  · intro hy w hw
    obtain ⟨p, hp⟩ := (mackeyPlaceEquiv S hL ι).surjective ⟨w, hw⟩
    have hw' : w = (Langlands.Galois.localPlace hL ι p.1 p.2.out).1 :=
      (congrArg Subtype.val hp).symm.trans (coe_mackeyPlaceEquiv hL ι p)
    subst hw'
    exact (map_mackeyFamily_eq_zero_iff_localization hL N ι ιL n p y).1 (hy p)
  · intro hy p
    exact (map_mackeyFamily_eq_zero_iff_localization hL N ι ιL n p y).2
      (hy _ (mackeyPlaceEquiv S hL ι p).2)

end Open

section Kummer

variable (ι : PlaceEmbeddings K Ω) [NeZero N]

/-- **`Ш²` of `μ_ℓ` over `P = G_S(L)`.** For a prime `ℓ = N` with the places above `ℓ` in `S`, and
`ℓ` odd or `L` totally complex, a class of `H²(P, μ_ℓ)` vanishes on the Mackey family of `P` exactly
when its image in `H²(P, 𝒪_Sˣ)` vanishes. -/
theorem mem_shaSubmodule_mackey_iff_coeffMap_eq_zero (hN : N.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hK : N ≠ 2 ∨ IsTotallyComplex L)
    (y : cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (dualizingModule K Ω S N)) 2) :
    y ∈ shaSubmodule (mackeyFamily (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
        (localFamily ι S)) (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (dualizingModule K Ω S N)) 2 ↔
      (coeffMap ((Rep.resFunctor (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype).map
          (rootsOfUnityToSUnits S (maximalUnramifiedOutside K Ω S) N)) 2).hom y = 0 := by
  have : IsSepClosure L Ω :=
    ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K L Ω⟩
  let ιL : PlaceEmbeddings L Ω := Classical.choice inferInstance
  have hSL : ∀ w : HeightOneSpectrum (𝓞 L), ((N : ℕ) : 𝓞 L) ∈ w.asIdeal →
      w ∈ finitePlacesAbove L S := fun w hw => by
    rw [mem_finitePlacesAbove_iff_under]
    refine hS _ ?_
    change algebraMap (𝓞 K) (𝓞 L) ((N : ℕ) : 𝓞 K) ∈ w.asIdeal
    rw [map_natCast]
    exact hw
  have key := mem_sha_iff_coeffMap_rootsOfUnityToSUnits_eq_zero ιL N hSL hN hK
    ((rootsOfUnityTransport hL N 2).hom y)
  rw [mem_sha, coeffMap_rootsOfUnityTransport] at key
  have hreal : ∀ w : InfinitePlace L, w.IsReal →
      realLocalization ιL (dualizingModule L Ω (finitePlacesAbove L S) N) w 2
        ((rootsOfUnityTransport hL N 2).hom y) = 0 := fun w hw => by
    rcases hK with ho | hc
    · exact eq_zero_cohomology_closureGalois_of_odd w hw _ (hN.odd_of_ne_two ho)
        (fun a => nsmul_dualizingModule (finitePlacesAbove L S) N a) (by norm_num) _
    · exact absurd hw (InfinitePlace.not_isReal_iff_isComplex.2 (hc.isComplex w))
  rw [mem_shaSubmodule_mackey_iff hL N ι ιL 2 y]
  constructor
  · intro h
    exact injective_map_resMaximalSUnitsHom hL 2 ((key.1 ⟨h, hreal⟩).trans (map_zero _).symm)
  · intro h
    exact (key.2 (by rw [h, map_zero])).1

end Kummer

end

end Langlands.GaloisCohomology
