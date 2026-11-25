import Langlands.GroupScheme.Reductive.AffineSplitSurjectionRootDatumStatement
import Langlands.GroupScheme.Reductive.IsogenyRootDatumProof
import Langlands.GroupScheme.Reductive.NoetherianIsogenyApproximation
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.CentralIsogeny.ProjectionCentralIsogeny
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection

/-! # The root-datum isogeny of a quasi-finite surjection on a field-valued fibre -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.AffineSplitSurjection

open CoordinateRootDatum Langlands.LinearAlgebra

section Lattice

variable {I I' : Type u} [Fintype I] [Fintype I'] {J J' : Type u} [Finite J] [Finite J']
  (k : Type u) [Field k]

omit [Finite J] in
/-- The field realization of a reduced coordinate root datum is reduced. -/
theorem isReduced_fieldRealization (P : RootDatum J (I → ℤ) (I → ℤ)) [hP : P.IsReduced] :
    (fieldRealization k P).IsReduced := by
  have hroot : ∀ α, (fieldRealization k P).root α =
      (splitTorus.characterLatticeEquiv k I).symm (P.root α) := fun α => by
    rw [fieldRealization_root, splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm]
  refine ⟨fun α β hdep => ?_⟩
  have hdep' : ¬ LinearIndependent ℤ ![P.root α, P.root β] := by
    intro hli
    apply hdep
    convert hli.map_injOn
      (splitTorus.characterLatticeEquiv k I).symm.toIntLinearEquiv.toLinearMap
      (splitTorus.characterLatticeEquiv k I).symm.injective.injOn using 1
    ext a
    fin_cases a <;> simp [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm]
  rcases hP.eq_or_eq_neg α β hdep' with h | h
  · left
    rw [hroot, hroot, h]
  · right
    rw [hroot, hroot, h, AddEquiv.map_neg]

variable {k}
variable {P : RootDatum J (I → ℤ) (I → ℤ)} {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  [P.IsReduced] [Q.IsReduced]
  [Module.Finite ℤ (characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I))]
  [Module.Finite ℤ
    (cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I))]
  [Module.Finite ℤ (characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I'))]
  [Module.Finite ℤ
    (cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I'))]

/-- Transport a root-datum isogeny between the field realizations of two coordinate root data
back to the coordinate root data themselves. -/
def ofFieldRealization {p : ℕ}
    [(fieldRealization k P).IsReduced] [(fieldRealization k Q).IsReduced]
    (f : RootDatumIsogeny p (fieldRealization k Q) (fieldRealization k P)) :
    RootDatumIsogeny p Q P :=
  (RootDatumIsogeny.ofHom f.characteristicExponent (fieldRealizationEquiv k P).symm.toHom
      (fieldRealizationEquiv k P).symm.bijective_weightMap.injective
      (fieldRealizationEquiv k P).symm.bijective_coweightMap.injective).comp
    (f.comp (RootDatumIsogeny.ofHom f.characteristicExponent (fieldRealizationEquiv k Q).toHom
      (fieldRealizationEquiv k Q).bijective_weightMap.injective
      (fieldRealizationEquiv k Q).bijective_coweightMap.injective))

/-- The weight map of the transported isogeny is computed through the exponent characters. -/
theorem ofFieldRealization_weightMap {p : ℕ}
    [(fieldRealization k P).IsReduced] [(fieldRealization k Q).IsReduced]
    (f : RootDatumIsogeny p (fieldRealization k Q) (fieldRealization k P))
    (h : (I' → ℤ) →ₗ[ℤ] (I → ℤ))
    (hf : ∀ m, f.weightMap (splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I' m) =
      splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (h m)) :
    (ofFieldRealization f).weightMap = h := by
  ext m : 1
  change (fieldRealizationEquiv k P).symm.weightMap
      (f.weightMap ((fieldRealizationEquiv k Q).weightMap m)) = h m
  rw [fieldRealizationEquiv_weightMap, hf, ← fieldRealizationEquiv_weightMap k P (h m)]
  exact (fieldRealizationEquiv k P).weightEquiv.symm_apply_apply (h m)

end Lattice

section TorusBaseChange

variable {S S' : Scheme.{u}} (b : S' ⟶ S) {I I' : Type u} [Fintype I] [Fintype I']

/-- The base change of a homomorphism of coordinate split tori along `b`, as a homomorphism
of the coordinate split tori over the new base. -/
def baseChangeTorusHom (τ : splitTorus S I ⟶ splitTorus S I') :
    splitTorus.commGroupScheme S' I ⟶ splitTorus.commGroupScheme S' I' :=
  Additive.ofMul ((splitTorus.baseChangeIso b I).inv ≫ (baseChange b).map τ ≫
    (splitTorus.baseChangeIso b I').hom)

/-- If `τ` pulls the exponent characters back by `h` over every test scheme landing in `V`,
then so does its base change along any `b` landing in `V`, as an identity of characters. -/
theorem baseChangeTorusHom_exponentCharacter (τ : splitTorus S I ⟶ splitTorus S I')
    {V : S.Opens} (hb : b ⁻¹ᵁ V = ⊤) {h : (I' → ℤ) →ₗ[ℤ] (I → ℤ)}
    (hV : ∀ (U : Over S), U.hom ⁻¹ᵁ V = ⊤ →
      ∀ (x : U ⟶ (splitTorus S I).X) (m : I' → ℤ),
        ∏ j', splitTorus.pointsEquiv I' U (x ≫ τ.hom.hom) j' ^ m j' =
          ∏ j, splitTorus.pointsEquiv I U x j ^ h m j)
    (m : I' → ℤ) :
    baseChangeTorusHom b τ ≫ splitTorus.exponentCharacter S' I' m =
      splitTorus.exponentCharacter S' I (h m) := by
  apply CommGroupScheme.hom_ext_points
  intro U x
  apply (Gm.pointsEquiv S' U).injective
  rw [comp_groupHom_comp, splitTorus.pointsEquiv_exponentCharacter,
    splitTorus.pointsEquiv_exponentCharacter]
  let x' := x ≫ (splitTorus.baseChangeIso b I).inv.hom.hom
  let z := GroupScheme.baseChangePointsEquiv b (splitTorus S I) U x'
  have hU : ((Over.map b).obj U).hom ⁻¹ᵁ V = ⊤ := by
    change U.hom ⁻¹ᵁ (b ⁻¹ᵁ V) = ⊤
    rw [hb]
    rfl
  have h1 : splitTorus.pointsEquiv I' U
      (x ≫ (CommGroupScheme.groupHom (baseChangeTorusHom b τ)).hom.hom) =
      splitTorus.pointsEquiv I' ((Over.map b).obj U) (z ≫ τ.hom.hom) := by
    change splitTorus.pointsEquiv I' U ((x' ≫ ((baseChange b).map τ).hom.hom) ≫
      (splitTorus.baseChangeIso b I').hom.hom.hom) = _
    rw [splitTorus.pointsEquiv_baseChangeIso_hom]
    change splitTorus.pointsEquiv I' ((Over.map b).obj U)
      (GroupScheme.baseChangePointsEquiv b _ U
        (x' ≫ ((Over.pullback b).mapGrp.map τ).hom.hom)) = _
    rw [GroupScheme.baseChangePointsEquiv_comp]
  have hid : (splitTorus.baseChangeIso b I).inv.hom.hom ≫
      (splitTorus.baseChangeIso b I).hom.hom.hom = 𝟙 _ :=
    congrArg (fun f => f.hom.hom) (splitTorus.baseChangeIso b I).inv_hom_id
  have h2 : splitTorus.pointsEquiv I ((Over.map b).obj U) z = splitTorus.pointsEquiv I U x := by
    change splitTorus.baseChangePointsEquiv b I U x' = _
    rw [← splitTorus.pointsEquiv_baseChangeIso_hom]
    change splitTorus.pointsEquiv I U ((x ≫ (splitTorus.baseChangeIso b I).inv.hom.hom) ≫
      (splitTorus.baseChangeIso b I).hom.hom.hom) = _
    rw [Category.assoc, hid, Category.comp_id]
  rw [h1, hV _ hU z m, h2]

end TorusBaseChange

section Field

variable {R : Type u} [CommRing R] {G H : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {I I' : Type u} [Fintype I] [Fintype I']
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H}
  {J J' : Type u} [Finite J] [Finite J']
  {P : RootDatum J (I → ℤ) (I → ℤ)} {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  [P.IsReduced] [Q.IsReduced]

/-- **Field form.** Over a field `k` whose spectrum lands in `V`, the quasi-finite surjection
`φ` becomes an isogeny of split connected reductive groups, and its root-datum isogeny,
transported to the coordinate root data, has weight map `h`. -/
theorem exists_rootDatumIsogeny_weightMap_of_field
    (hG : IsReductive G) (hH : IsReductive H)
    (hmax : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hmax' : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I') i')
    (hQ : IsFibrewiseRootDatumOf I' H i' Q)
    {φ : G ⟶ H}
    {τ : splitTorus (Spec (CommRingCat.of R)) I ⟶ splitTorus (Spec (CommRingCat.of R)) I'}
    (hφ : LocallyQuasiFinite φ.hom.hom.left) (hsurj : Surjective φ.hom.hom.left)
    (hsq : i ≫ φ = τ ≫ i')
    {V : (Spec (CommRingCat.of R)).Opens} {h : (I' → ℤ) →ₗ[ℤ] (I → ℤ)}
    (hV : ∀ (U : Over (Spec (CommRingCat.of R))), U.hom ⁻¹ᵁ V = ⊤ →
      ∀ (x : U ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (m : I' → ℤ),
        ∏ j', splitTorus.pointsEquiv I' U (x ≫ τ.hom.hom) j' ^ m j' =
          ∏ j, splitTorus.pointsEquiv I U x j ^ h m j)
    (k : Type u) [Field k] [Algebra R k] (hk : algebraBaseMap R k ⁻¹ᵁ V = ⊤) :
    ∃ (p : ℕ) (r : RootDatumIsogeny p Q P), r.weightMap = h := by
  have := hG.smooth
  have := hH.smooth
  let b := algebraBaseMap R k
  let Gk := (baseChange b).obj G
  let Hk := (baseChange b).obj H
  let φk : Gk ⟶ Hk := (baseChange b).map φ
  have hGk : IsConnectedReductive Gk := hG.isConnectedReductive_baseChange b
  have hHk : IsConnectedReductive Hk := hH.isConnectedReductive_baseChange b
  have hT : IsSplitTorus (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I).toGrp :=
    isSplitTorus_splitTorus I
  have hT' : IsSplitTorus (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I').toGrp :=
    isSplitTorus_splitTorus I'
  have := hT.finite_characterLattice
  have := hT.finite_cocharacterLattice
  have := hT'.finite_characterLattice
  have := hT'.finite_cocharacterLattice
  -- `φ` becomes an isogeny over `k`.
  have hpb := baseChange_map_isPullback b φ
  have : QuasiCompact φ.hom.hom.left := by
    have : QuasiCompact (φ.hom.hom.left ≫ H.X.hom) := by
      rw [Over.w φ.hom.hom]
      infer_instance
    exact QuasiCompact.of_comp φ.hom.hom.left H.X.hom
  have : QuasiCompact φk.hom.hom.left := MorphismProperty.of_isPullback hpb.flip inferInstance
  have : LocallyQuasiFinite φk.hom.hom.left := MorphismProperty.of_isPullback hpb.flip hφ
  have : Surjective φk.hom.hom.left := MorphismProperty.of_isPullback hpb.flip hsurj
  have : LocallyOfFiniteType Gk.X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom b)
    infer_instance
  have : QuasiCompact Gk.X.hom := by
    change QuasiCompact (pullback.snd G.X.hom b)
    infer_instance
  have : Smooth Hk.X.hom := by
    change Smooth (pullback.snd H.X.hom b)
    infer_instance
  have : Flat φk.hom.hom.left := flat_of_surjective φk
  have hisog : IsIsogeny φk := isogeny_of_quasiFinite_flat_surjective_over_field φk
  -- The torus square over `k`.
  let t := baseChangeTorusHom b τ
  have hsqk : splitTorus.baseChangeHom (K := k) G I i ≫ φk =
      CommGroupScheme.groupHom t ≫ splitTorus.baseChangeHom (K := k) H I' i' := by
    change ((splitTorus.baseChangeIso b I).inv ≫ (baseChange b).map i) ≫ (baseChange b).map φ =
      ((splitTorus.baseChangeIso b I).inv ≫ (baseChange b).map τ ≫
        (splitTorus.baseChangeIso b I').hom) ≫
        (splitTorus.baseChangeIso b I').inv ≫ (baseChange b).map i'
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hsq]
  have := isReduced_fieldRealization k P
  have := isReduced_fieldRealization k Q
  obtain ⟨-, f, hf, -⟩ := isogenyRootDatum k Gk Hk hGk hHk
    (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
    (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I') hT hT'
    (splitTorus.baseChangeHom (K := k) G I i) (splitTorus.baseChangeHom (K := k) H I' i')
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hmax k)
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I' H i' hmax' k)
    φk t hisog hsqk J J' (fieldRealization k P) (fieldRealization k Q) (hP.field k) (hQ.field k)
  refine ⟨_, ofFieldRealization f, ofFieldRealization_weightMap f h fun m => ?_⟩
  rw [hf]
  exact baseChangeTorusHom_exponentCharacter b τ hk hV m

/-- **Point form.** At every point `s ∈ V`, the residue field `κ(s)` yields a root-datum
isogeny `Q → P` whose weight map is `h`. -/
theorem exists_rootDatumIsogeny_weightMap
    (hG : IsReductive G) (hH : IsReductive H)
    (hmax : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hmax' : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I') i')
    (hQ : IsFibrewiseRootDatumOf I' H i' Q)
    {φ : G ⟶ H}
    {τ : splitTorus (Spec (CommRingCat.of R)) I ⟶ splitTorus (Spec (CommRingCat.of R)) I'}
    (hφ : LocallyQuasiFinite φ.hom.hom.left) (hsurj : Surjective φ.hom.hom.left)
    (hsq : i ≫ φ = τ ≫ i')
    {V : (Spec (CommRingCat.of R)).Opens} {h : (I' → ℤ) →ₗ[ℤ] (I → ℤ)}
    (hV : ∀ (U : Over (Spec (CommRingCat.of R))), U.hom ⁻¹ᵁ V = ⊤ →
      ∀ (x : U ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (m : I' → ℤ),
        ∏ j', splitTorus.pointsEquiv I' U (x ≫ τ.hom.hom) j' ^ m j' =
          ∏ j, splitTorus.pointsEquiv I U x j ^ h m j)
    (s : Spec (CommRingCat.of R)) (hs : s ∈ V) :
    ∃ (p : ℕ) (r : RootDatumIsogeny p Q P), r.weightMap = h := by
  let s' : PrimeSpectrum R := s
  refine exists_rootDatumIsogeny_weightMap_of_field hG hH hmax hP hmax' hQ hφ hsurj hsq hV
    s'.asIdeal.ResidueField ?_
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : (algebraBaseMap R s'.asIdeal.ResidueField).base x = s := by
    let x' : PrimeSpectrum s'.asIdeal.ResidueField := x
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R s'.asIdeal.ResidueField) x'.asIdeal = s'.asIdeal
    rw [Ideal.eq_bot_of_prime x'.asIdeal, ← RingHom.ker_eq_comap_bot,
      Ideal.ker_algebraMap_residueField]
  change (algebraBaseMap R s'.asIdeal.ResidueField).base x ∈ V
  rw [hx]
  exact hs

end Field

end Langlands.GroupScheme.AffineSplitSurjection
