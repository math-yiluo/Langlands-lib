import Langlands.Geometry.Building.SplitIntegralPinningOfRoots
import Langlands.Geometry.Building.IntegerCentralizerStabilizer
import Langlands.GroupScheme.IntegralModel.SplitIntegralPoints
import Langlands.GroupScheme.Reductive.StrictHenselianGenericIsoProof
import Langlands.GroupScheme.Reductive.LocalSplitRootDatumExistence
import Langlands.GroupScheme.Reductive.LocalSplitRootGroupProof
import Langlands.GroupScheme.Reductive.LocalSplitIntegralGeneration
import Langlands.GroupScheme.Reductive.LocalSplitFieldPoints
import Langlands.GroupScheme.Reductive.LocalSplitRootTransport
import Langlands.GroupScheme.Reductive.LocalRootGroupFibre
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.RelativeAdjointWeightBaseChange
import Langlands.Geometry.Building.KPWeilRestrictionUnitKernel
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.IntegralModel.ClosedSubgroupIntegralPoints

/-! # Split integral pinnings of the generic fibre of a strictly Henselian reductive model -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-! ### Transport along an isomorphism of the ambient group -/

section AmbientIso

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- A normalizing point stays normalizing after an isomorphism of the ambient groups. -/
theorem IsNormalizingPoint.comp_iso {i : T.toGrp ⟶ G} {n : Over.mk (𝟙 _) ⟶ G.X} {σ : T ≅ T}
    (h : IsNormalizingPoint i n σ) (Φ : G ≅ H) :
    IsNormalizingPoint (i ≫ Φ.hom) (n ≫ Φ.hom.hom.hom) σ := by
  unfold IsNormalizingPoint at h ⊢
  rw [Category.assoc, ← innerIso_hom_comp, ← Category.assoc, h, Category.assoc]

variable [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- A root datum of a torus stays its root datum after an isomorphism of the ambient groups. -/
theorem IsRootDatumOf.comp_iso {J : Type*} {i : T.toGrp ⟶ G}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)} (hP : IsRootDatumOf i P)
    (Φ : G ≅ H) : IsRootDatumOf (i ≫ Φ.hom) P := by
  refine ⟨hP.1, ?_, fun α => ?_⟩
  · have hs : i ≫ Φ.hom = CommGroupScheme.groupHom (Iso.refl T).hom ≫ (i ≫ Φ.hom) :=
      (Category.id_comp _).symm
    have hchar : ⇑(characterLattice.congr (Iso.refl T)) = id := by
      funext a
      exact Category.id_comp a
    rw [hP.2.1, ← roots_image_of_transport (Iso.refl T) Φ hs, hchar, Set.image_id]
  · obtain ⟨n, σ, hn, hσ⟩ := hP.2.2 α
    exact ⟨n ≫ Φ.hom.hom.hom, σ, hn.comp_iso Φ, hσ⟩

end AmbientIso

section WeylIso

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {G H : GroupScheme (Spec (CommRingCat.of R))}

open LocalSplitCell

/-- A Weyl point stays a Weyl point after an isomorphism of the ambient groups. -/
theorem LocalSplitCell.IsWeylPoint.comp_iso {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {u v : Ga R ⟶ G} {f : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)} (h : IsWeylPoint i (weylPoint u v) f)
    (Φ : G ≅ H) : IsWeylPoint (i ≫ Φ.hom) (weylPoint (u ≫ Φ.hom) (v ≫ Φ.hom)) f := by
  intro Z t
  rw [weylPoint_comp, Grp.comp_hom_hom, ← Category.assoc t,
    ← Category.assoc (SemiCartesianMonoidalCategory.toUnit Z),
    ← GrpObj.inv_comp, ← MonObj.mul_comp, ← MonObj.mul_comp, h Z t]
  simp only [Category.assoc]

end WeylIso

/-! ### Generic fibres of integral split tori and root groups -/

namespace IntegralModel

open LocalSplitCell LocalSplitBigCell Langlands.Geometry.Building

section Generic

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {H : GroupScheme (Spec (CommRingCat.of K))} (N : IntegralModel R K H)
  {I : Type u} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
/-- The generic split torus map is the base-changed torus map followed by the generic
identification. -/
theorem genericSplitTorusHom_eq (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ N.group) :
    N.genericSplitTorusHom i =
      splitTorus.baseChangeHom (K := K) N.group I i ≫ N.genericIso.hom := by
  rw [genericSplitTorusHom, genericHom, splitTorus.baseChangeHom, Category.assoc]

/-- The generic root map is the base-changed root map followed by the generic
identification. -/
theorem genericRootHom_eq (u : Ga R ⟶ N.group) :
    N.genericRootHom u = baseChangeRoot K u ≫ N.genericIso.hom := by
  rw [genericRootHom, genericHom, baseChangeRoot, Category.assoc]

/-- Field values of the generic root map are the generic root values. -/
theorem fieldRootPoint_genericRootHom (u : Ga R ⟶ N.group) (c : K) :
    SplitIntegralPinning.fieldRootPoint (N.genericRootHom u) c = N.genericRootValue u c :=
  rfl

end Generic

/-! ### Maximality, roots and Weyl points on the generic fibre -/

section GenericRoots

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {H : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom H.X.hom] (N : IntegralModel R K H)
  [Smooth N.group.X.hom] [IsAffineHom N.group.X.hom]
  {I : Type u} [Fintype I] (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ N.group)

omit [IsAffineHom H.X.hom] in
/-- A fibrewise maximal integral split torus has a maximal torus as generic fibre. -/
theorem isMaximalTorus_genericSplitTorusHom
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i) :
    IsMaximalTorus (T := SplitIntegralPinning.coordTorus K I) (N.genericSplitTorusHom i) := by
  rw [genericSplitTorusHom_eq]
  exact (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I N.group i hmax K).comp_iso
    N.genericIso

omit [IsAffineHom H.X.hom] in
/-- A fibrewise maximal integral split torus has a maximal split torus as generic fibre. -/
theorem isMaximalSplitTorus_genericSplitTorusHom
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i) :
    IsMaximalSplitTorus (T := SplitIntegralPinning.coordTorus K I) (N.genericSplitTorusHom i) :=
  (N.isMaximalTorus_genericSplitTorusHom i hmax).isMaximalSplitTorus
    (isSplitTorus_splitTorus I)

omit [Smooth N.group.X.hom] in
/-- A fibrewise root datum of an integral split torus is the root datum of its generic fibre. -/
theorem isRootDatumOf_genericSplitTorusHom {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hP : IsFibrewiseRootDatumOf I N.group i P) :
    IsRootDatumOf (T := SplitIntegralPinning.coordTorus K I) (N.genericSplitTorusHom i)
      (CoordinateRootDatum.fieldRealization K P) := by
  rw [genericSplitTorusHom_eq]
  exact (hP.field K).comp_iso N.genericIso

omit [IsAffineHom H.X.hom] [Smooth N.group.X.hom] [IsAffineHom N.group.X.hom] in
/-- Root parametrizations of an integral split torus give root parametrizations of its generic
fibre. -/
theorem isRootParametrization_genericRootHom {m : I → ℤ} {u : Ga R ⟶ N.group}
    (hu : IsRootParametrization i m u) :
    IsRootParametrization (N.genericSplitTorusHom i) m (N.genericRootHom u) := by
  rw [genericSplitTorusHom_eq, genericRootHom_eq]
  exact (isRootParametrization_baseChangeRoot K i m u hu).comp_iso N.genericIso rfl

omit [IsAffineHom H.X.hom] [Smooth N.group.X.hom] [IsAffineHom N.group.X.hom] in
variable [DecidableEq I] in
/-- Weyl points of an integral split torus give Weyl points of its generic fibre. -/
theorem isWeylPoint_genericRootHom {u u' : Ga R ⟶ N.group} {f : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)}
    (h : IsWeylPoint i (weylPoint u u') f) :
    IsWeylPoint (N.genericSplitTorusHom i)
      (weylPoint (N.genericRootHom u) (N.genericRootHom u')) f := by
  rw [genericSplitTorusHom_eq, genericRootHom_eq, genericRootHom_eq]
  exact (IsWeylPoint.baseChange (K := K) h).comp_iso N.genericIso

end GenericRoots

/-! ### Integral points in terms of a valuation -/

section Valuation

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {H : GroupScheme (Spec (CommRingCat.of K))} (N : IntegralModel R K H)
  (v : Valuation K (WithZero (Multiplicative ℤ)))
  (hv : ∀ c : K, v c ≤ 1 ↔ c ∈ (algebraMap R K).range)

omit [IsDomain R] [IsFractionRing R K] in
include hv in
/-- Units of `R` have valuation one when `R` is the valuation ring of `v`. -/
theorem valuation_algebraMap_unit (s : Rˣ) : v (algebraMap R K s) = 1 := by
  have h1 : v (algebraMap R K s) ≤ 1 := (hv _).2 ⟨s, rfl⟩
  have h2 : v (algebraMap R K ↑s⁻¹) ≤ 1 := (hv _).2 ⟨_, rfl⟩
  have h3 : v (algebraMap R K s) * v (algebraMap R K ↑s⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = v (algebraMap R K s) * v (algebraMap R K ↑s⁻¹) :=
        h3.symm
    _ ≤ v (algebraMap R K s) * 1 := by gcongr
    _ = v (algebraMap R K s) := mul_one _

omit [IsDomain R] [IsFractionRing R K] in
/-- Restricting a global function on `Spec R` to `Spec K` is the algebra map on rings. -/
theorem ΓSpecIso_hom_appTop (r : Γ(Spec (CommRingCat.of R), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((Spec.algebraMap R K).appTop r) =
      algebraMap R K ((Scheme.ΓSpecIso (CommRingCat.of R)).hom r) :=
  congrArg (fun f => f.hom r) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R K)))

include hv in
/-- A generic root value of a closed root group is integral exactly when its coordinate has
valuation at most one. -/
theorem fieldRootPoint_genericRootHom_mem_integralPoints_iff (u : Ga R ⟶ N.group)
    (hu : IsClosedSubgroup u) (c : K) :
    SplitIntegralPinning.fieldRootPoint (N.genericRootHom u) c ∈ N.integralPoints ↔ v c ≤ 1 := by
  rw [fieldRootPoint_genericRootHom, N.genericRootValue_mem_integralPoints_iff u hu, hv]

include hv in
/-- The integral image of an integral point of a split torus is the generic image of a point
of the character-valuation kernel of the coordinate torus. -/
theorem integralPointMap_map_mem_image {I : Type u} [Fintype I]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ N.group)
    (t : rationalPoints (splitTorus (Spec (CommRingCat.of R)) I)) :
    N.integralPointMap (rationalPoints.map i t) ∈ rationalPoints.map (N.genericSplitTorusHom i) ''
      (characterValuationKernel v (SplitIntegralPinning.coordTorus K I).toGrp : Set _) := by
  refine ⟨baseChangeSectionHom (Spec.algebraMap R K) _ t ≫
    (splitTorus.baseChangeIso (Spec.algebraMap R K) I).hom.hom.hom, ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_split_characterValuationKernel]
    intro j
    change v ((Scheme.ΓSpecIso (CommRingCat.of K)).hom
      ((splitTorus.pointsEquiv I (Over.mk (𝟙 (Spec (CommRingCat.of K))))
        (baseChangeSectionHom (Spec.algebraMap R K) _ t ≫
          (splitTorus.baseChangeIso (Spec.algebraMap R K) I).hom.hom.hom) j).val)) = 1
    rw [pointsEquiv_baseChangeSectionHom, Units.coe_map]
    change v ((Scheme.ΓSpecIso (CommRingCat.of K)).hom
      ((Spec.algebraMap R K).appTop _)) = 1
    rw [ΓSpecIso_hom_appTop]
    exact valuation_algebraMap_unit v hv (Units.map
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom
      (splitTorus.pointsEquiv I (Over.mk (𝟙 (Spec (CommRingCat.of R)))) t j))
  · change (baseChangeSectionHom (Spec.algebraMap R K) _ t ≫
      (splitTorus.baseChangeIso (Spec.algebraMap R K) I).hom.hom.hom) ≫
        ((splitTorus.baseChangeIso (Spec.algebraMap R K) I).inv ≫ N.genericHom i).hom.hom =
      N.subgroupPointMap i t
    rw [N.subgroupPointMap_apply, Grp.comp_hom_hom, Category.assoc,
      ← Category.assoc (splitTorus.baseChangeIso (Spec.algebraMap R K) I).hom.hom.hom,
      ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom, Category.id_comp]
    rfl

include hv in
/-- Over a strictly Henselian local domain, the integral points of a reductive model lie in the
subgroup generated by the bounded torus points and the integral root values of a fibrewise
maximal split torus with root parametrizations. -/
theorem integralPoints_le_closure [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)] [IsAffineHom N.group.X.hom]
    (hN : IsReductive N.group) {I J : Type u} [Fintype I] [DecidableEq I]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ N.group) (hic : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (P : RootDatum J (I → ℤ) (I → ℤ)) (hP : IsFibrewiseRootDatumOf I N.group i P) (b : P.Base)
    (u : J → (Ga R ⟶ N.group)) (hu : ∀ α, IsRootParametrization i (P.root α) (u α)) :
    N.integralPoints ≤ Subgroup.closure
      (rationalPoints.map (N.genericSplitTorusHom i) ''
          (characterValuationKernel v (SplitIntegralPinning.coordTorus K I).toGrp : Set _) ∪
        ⋃ α, SplitIntegralPinning.fieldRootPoint (N.genericRootHom (u α)) '' {c | v c ≤ 1}) := by
  rintro _ ⟨x, rfl⟩
  have hx := LocalSplitCell.mem_closure_generators hN i hic hmax P hP b u hu x
  have hmem : N.integralPointMap x ∈
      (Subgroup.closure (LocalSplitCell.generators i u)).map N.integralPointMap :=
    ⟨x, hx, rfl⟩
  rw [MonoidHom.map_closure] at hmem
  refine (Subgroup.closure_le _).2 ?_ hmem
  rintro _ ⟨g, hg, rfl⟩
  rcases hg with ⟨t, rfl⟩ | hg
  · exact Subgroup.subset_closure (Or.inl (N.integralPointMap_map_mem_image v hv i t))
  · obtain ⟨α, r, rfl⟩ := Set.mem_iUnion.1 hg
    apply Subgroup.subset_closure
    refine Or.inr (Set.mem_iUnion.2 ⟨α,
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((Spec.algebraMap R K).appTop r), ?_, ?_⟩)
    · change v _ ≤ 1
      rw [ΓSpecIso_hom_appTop, hv]
      exact ⟨_, rfl⟩
    · change LocalSplitCell.rootPoint (N.genericRootHom (u α)) (Over.mk (𝟙 _))
        (SplitIntegralPinning.baseRingEquiv _) = _
      rw [SplitIntegralPinning.baseRingEquiv_apply,
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply]
      exact (N.integralPointMap_rootPoint (u α) r).symm

end Valuation

/-! ### The split integral pinning of the generic fibre -/

section Pinning

variable {R K : Type u} [CommRing R] [IsDomain R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K]
  {H : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom H.X.hom] (N : IntegralModel R K H)
  (v : Valuation K (WithZero (Multiplicative ℤ)))
  (hv : ∀ c : K, v c ≤ 1 ↔ c ∈ (algebraMap R K).range)

include hv in
/-- **Split integral pinning of the generic fibre of a strictly Henselian reductive model.**
Let `R` be a strictly Henselian local domain which is the valuation ring of `v` on its
fraction field `K`, and `N` a reductive model over `R` of a connected reductive `K`-group.
For a closed fibrewise maximal split torus `i` of `N` with a fibrewise root datum `P`, a base
`b`, root parametrizations `u` and simple Weyl points, the generic fibre of `i` carries a split
integral pinning whose subgroup is the group of integral points of `N`, provided the
torus-integrality input `hK_torus` of `SplitIntegralPinning.ofRootParametrizations` holds. -/
theorem exists_splitIntegralPinning_genericSplitTorusHom (hH : IsConnectedReductive H)
    (hN : IsReductive N.group) {I : Type u} [Fintype I] [DecidableEq I]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ N.group) (hic : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J : Type u} (P : RootDatum J (I → ℤ) (I → ℤ)) (hP : IsFibrewiseRootDatumOf I N.group i P)
    (b : P.Base) (u : J → (Ga R ⟶ N.group))
    (hu : ∀ α, IsRootParametrization i (P.root α) (u α))
    (hw : ∀ a ∈ b.support,
      IsWeylPoint i (weylPoint (u a) (u (P.reflectionPerm a a))) (P.reflection a))
    (hK_torus : ∀ t : rationalPoints (SplitIntegralPinning.coordTorus K I).toGrp,
      (∀ a ∈ relativeRoots (T := SplitIntegralPinning.coordTorus K I) (N.genericSplitTorusHom i),
        IntegerValuation.order v (torusCharEval (SplitIntegralPinning.coordTorus K I) a t) = 0) →
      rationalPoints.map (N.genericSplitTorusHom i) t ∈ characterValuationKernel v H →
      rationalPoints.map (N.genericSplitTorusHom i) t ∈ N.integralPoints) :
    ∃ (_ : Mono (N.genericSplitTorusHom i).hom.hom.left)
      (Pin : SplitIntegralPinning (S := SplitIntegralPinning.coordTorus K I) v
        (N.genericSplitTorusHom i)), Pin.K = N.integralPoints := by
  let := hN.smooth
  let := hN.isAffineHom
  have hi := N.isMaximalTorus_genericSplitTorusHom i hmax
  have hmono : Mono (N.genericSplitTorusHom i).hom.hom.left :=
    mono_of_isMaximalSplitTorus (N.isMaximalSplitTorus_genericSplitTorusHom i hmax)
  let : Fintype J := @Fintype.ofFinite J hP.finite
  exact ⟨hmono, SplitIntegralPinning.ofRootParametrizations v hH hi hP.isReduced
    (N.isRootDatumOf_genericSplitTorusHom i hP) b
    (fun α => N.isRootParametrization_genericRootHom i (hu α))
    (fun j hj => N.isWeylPoint_genericRootHom i (hw j hj)) N.integralPoints
    (fun α c => N.fieldRootPoint_genericRootHom_mem_integralPoints_iff v hv _
      (hu α).isClosedSubgroup c)
    hK_torus (N.integralPoints_le_closure v hv hN i hic hmax P hP b u hu), rfl⟩

end Pinning

end IntegralModel

end Langlands.GroupScheme
