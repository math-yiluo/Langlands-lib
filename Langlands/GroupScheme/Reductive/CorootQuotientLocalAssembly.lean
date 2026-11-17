import Langlands.GroupScheme.Reductive.CorootQuotientGeometricKernel
import Langlands.GroupScheme.Reductive.CorootCellExtensionGeometry
import Langlands.GroupScheme.Reductive.AffinePinnedCentralizer
import Langlands.GroupScheme.Reductive.AffinePinnedScalarExtension
import Langlands.GroupScheme.Reductive.RelativeDerivedSplitReduction
import Langlands.GroupScheme.Reductive.LocalSplitLocalAlgebraCellIsomorphism
import Langlands.GroupScheme.Dynamic.BaseTripleCell
import Langlands.GroupScheme.Dynamic.BaseSmoothConnectedProof
import Langlands.GroupScheme.Dynamic.Uniqueness

/-! # Assembling coroot quotient maps from local coefficient rings -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace Dynamic

/-- A homomorphism to a separated commutative group kills the full dynamic
identity-limit subgroup, on every scheme test. -/
theorem comp_eq_one_of_mem_unipotent_to_comm
    {S : Scheme.{u}} {G : GroupScheme S} {Q : CommGroupScheme S}
    [IsSeparated Q.X.hom] (χ : (Gm S).toGrp ⟶ G) (q : G ⟶ Q.toGrp)
    {T : Over S} {x : T ⟶ G.X} (hx : x ∈ (unipotent χ).carrier T) :
    x ≫ q.hom.hom = 1 := by
  have hu := unipotent_le_comap χ q T hx
  have hz : x ≫ q.hom.hom ∈ (centralizer (χ ≫ q)).carrier T := by
    rw [mem_centralizer, orbit]
    simp [mul_comm, mul_assoc]
  exact eq_one_of_mem_centralizer_of_mem_unipotent (χ ≫ q)
    (fun _ _ _ _ h h' => h.unique _ h') hz hu

end Dynamic

namespace RelativeDerived

section PointMaps

variable {S S' : Scheme.{u}} (b : S' ⟶ S)
  {G H : GroupScheme S} {Q : CommGroupScheme S'}
  (q : (GroupScheme.baseChange b).obj G ⟶ Q.toGrp)
  (e : (GroupScheme.baseChange b).obj H ≅ Q.toGrp)
  (T : Over S')

/-- A supplied homomorphism on a pullback induces a homomorphism on the
corresponding original-base points via the actual pullback adjunction. -/
def pullbackPointHom :
    (((Over.map b).obj T) ⟶ G.X) →* (((Over.map b).obj T) ⟶ H.X) :=
  (baseChangePointsEquiv b H T).toMonoidHom.comp
    (((yonedaGrp.map (q ≫ e.inv)).app (op T)).hom.comp
      (baseChangePointsEquiv b G T).symm.toMonoidHom)

/-- A prescribed restriction of the pullback homomorphism gives the identical
restriction on original-base points. -/
theorem pullbackPointHom_restrict {L : GroupScheme S} (i : L ⟶ G) (p : L ⟶ H)
    (hq : (GroupScheme.baseChange b).map i ≫ q =
      (GroupScheme.baseChange b).map p ≫ e.hom)
    (x : ((Over.map b).obj T) ⟶ L.X) :
    pullbackPointHom b q e T (x ≫ i.hom.hom) = x ≫ p.hom.hom := by
  let y := (baseChangePointsEquiv b L T).symm x
  have hx : x ≫ i.hom.hom =
      baseChangePointsEquiv b G T (y ≫ ((GroupScheme.baseChange b).map i).hom.hom) := by
    rw [baseChangePointsEquiv_comp]
    simp only [y, MulEquiv.apply_symm_apply]
  rw [hx]
  change baseChangePointsEquiv b H T
    (((baseChangePointsEquiv b G T).symm
      (baseChangePointsEquiv b G T
        (y ≫ ((GroupScheme.baseChange b).map i).hom.hom))) ≫ (q ≫ e.inv).hom.hom) =
      x ≫ p.hom.hom
  rw [MulEquiv.symm_apply_apply]
  have heq : (GroupScheme.baseChange b).map i ≫ (q ≫ e.inv) =
      (GroupScheme.baseChange b).map p := by
    rw [← Category.assoc, hq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [Category.assoc, ← Grp.comp_hom_hom, heq, baseChangePointsEquiv_comp]
  simp only [y, MulEquiv.apply_symm_apply]

/-- The point homomorphism kills original dynamic unipotent points even when
the supplied pullback map has a differently normalized target. -/
theorem pullbackPointHom_unipotent [IsSeparated Q.X.hom]
    (χ : (Gm S).toGrp ⟶ G) {x : ((Over.map b).obj T) ⟶ G.X}
    (hx : x ∈ (Dynamic.unipotent χ).carrier ((Over.map b).obj T)) :
    pullbackPointHom b q e T x = 1 := by
  let y := (baseChangePointsEquiv b G T).symm x
  have hy : y ∈ (Dynamic.unipotent (Dynamic.baseChangeCocharacter b χ)).carrier T := by
    rw [Dynamic.unipotent_baseChange]
    change baseChangePointsEquiv b G T y ∈
      (Dynamic.unipotent χ).carrier ((Over.map b).obj T)
    simpa only [y, MulEquiv.apply_symm_apply] using hx
  have hkill := Dynamic.comp_eq_one_of_mem_unipotent_to_comm
    (Dynamic.baseChangeCocharacter b χ) q hy
  change baseChangePointsEquiv b H T (y ≫ (q ≫ e.inv).hom.hom) = 1
  rw [Grp.comp_hom_hom, ← Category.assoc, hkill, MonObj.one_comp, map_one]

/-- The transported homomorphism has the coroot-cell formula whenever its
restriction is prescribed and the outer factors represent dynamic unipotents. -/
theorem pullbackPointHom_tripleCell [IsSeparated Q.X.hom]
    (χ : (Gm S).toGrp ⟶ G) {N L U : GroupScheme S}
    (iN : N ⟶ G) (iL : L ⟶ G) (iU : U ⟶ G)
    (hN : (Dynamic.unipotent
      (CommGroupScheme.groupHom (Gm.powerHom S (-1)) ≫ χ)).IsRepresentedBy iN)
    (hU : (Dynamic.unipotent χ).IsRepresentedBy iU)
    (p : L ⟶ H)
    (hq : (GroupScheme.baseChange b).map iL ≫ q =
      (GroupScheme.baseChange b).map p ≫ e.hom)
    (x : ((Over.map b).obj T) ⟶ N.X ⊗ (L.X ⊗ U.X)) :
    pullbackPointHom b q e T (x ≫ Dynamic.tripleCellMultiplication iN iL iU) =
      x ≫ snd _ _ ≫ fst _ _ ≫ p.hom.hom := by
  let n := x ≫ fst N.X (L.X ⊗ U.X)
  let l := x ≫ snd N.X (L.X ⊗ U.X) ≫ fst L.X U.X
  let v := x ≫ snd N.X (L.X ⊗ U.X) ≫ snd L.X U.X
  have hn : n ≫ iN.hom.hom ∈
      (Dynamic.unipotent
        (CommGroupScheme.groupHom (Gm.powerHom S (-1)) ≫ χ)).carrier _ := by
    rw [← hN.2, SubgroupFunctor.mem_range]
    exact ⟨n, rfl⟩
  have hv : v ≫ iU.hom.hom ∈ (Dynamic.unipotent χ).carrier _ := by
    rw [← hU.2, SubgroupFunctor.mem_range]
    exact ⟨v, rfl⟩
  have hx : x = lift n (lift l v) := by
    simp only [n, l, v, ← comp_lift, lift_fst_snd, Category.comp_id]
  rw [hx, Dynamic.lift_tripleCellMultiplication, map_mul, map_mul,
    pullbackPointHom_unipotent b q e T _ hn,
    pullbackPointHom_unipotent b q e T χ hv,
    pullbackPointHom_restrict b q e T iL p hq l, one_mul, mul_one]
  simp only [lift_snd_assoc, lift_fst_assoc, l]

end PointMaps

end RelativeDerived

/-- The local coefficient-ring input needed for coroot quotient assembly.
No smoothness or surjectivity of the supplied homomorphism is assumed. -/
def RelativeDerivedLocalCorootQuotientExistenceStatement : Prop :=
  ∀ (M : AffinePinnedModel.{u}) [DecidableEq M.coordinates] [IsLocalRing M.ring],
    ∃ q : M.group ⟶
      (RelativeDerived.corootQuotient (CommRingCat.of M.ring) M.rootDatum).toGrp,
      M.inclusion ≫ q =
        RelativeDerived.corootProjection (CommRingCat.of M.ring) M.rootDatum

namespace RelativeDerived

/-- Local coefficient-ring witnesses suffice for compatibility of the
canonical dynamic cell with the actual coroot projection. -/
theorem cellCompatible_dynamic_of_localCorootQuotient
    (hlocal : RelativeDerivedLocalCorootQuotientExistenceStatement.{u})
    (M : AffinePinnedModel.{u}) [DecidableEq M.coordinates]
    {N U : GroupScheme M.base} (iN : N ⟶ M.group) (iU : U ⟶ M.group)
    (hN : (Dynamic.unipotent
      (CommGroupScheme.groupHom (Gm.powerHom M.base (-1)) ≫
        BasedBorelTransport.cocharacter M.inclusion M.rootDatum M.basis)).IsRepresentedBy iN)
    (hU : (Dynamic.unipotent
      (BasedBorelTransport.cocharacter M.inclusion M.rootDatum M.basis)).IsRepresentedBy iU)
    [IsOpenImmersion (Dynamic.tripleCellMultiplication iN M.inclusion iU).left] :
    CellGluing.CellCompatible
      (Dynamic.tripleCellMultiplication iN M.inclusion iU)
      (snd N.X ((splitTorus M.base M.coordinates).X ⊗ U.X) ≫
        fst (splitTorus M.base M.coordinates).X U.X ≫
          (corootProjection (CommRingCat.of M.ring) M.rootDatum).hom.hom) := by
  let p := corootProjection (CommRingCat.of M.ring) M.rootDatum
  let χ := BasedBorelTransport.cocharacter M.inclusion M.rootDatum M.basis
  let : IsAffine (corootQuotient (CommRingCat.of M.ring) M.rootDatum).X.left :=
    isAffine_of_isAffineHom
      (corootQuotient (CommRingCat.of M.ring) M.rootDatum).X.hom
  apply CellGluing.cellCompatible_of_localRingPoints
  intro A _ _ s x y c hxy
  let : Algebra M.ring A := (Spec.preimage s).hom.toAlgebra
  have hs : algebraBaseMap M.ring A = s := Spec.map_preimage s
  let : IsLocalRing (M.scalarExtension A).ring := inferInstanceAs (IsLocalRing A)
  obtain ⟨q, hq⟩ := hlocal (M.scalarExtension A)
  change ((splitTorus.baseChangeIso (algebraBaseMap M.ring A) M.coordinates).inv ≫
    (baseChange (algebraBaseMap M.ring A)).map M.inclusion) ≫ q =
      corootProjection (CommRingCat.of A) M.rootDatum at hq
  let e := Diagonalizable.baseChangeIso (algebraBaseMap M.ring A)
    (cocenterLattice M.rootDatum)
  have hq' : (baseChange (algebraBaseMap M.ring A)).map M.inclusion ≫ q =
      (baseChange (algebraBaseMap M.ring A)).map p ≫ e.hom := by
    rw [corootProjection_baseChange_square]
    rw [← hq, ← Category.assoc, Iso.hom_inv_id_assoc]
  let T : Over (Spec (CommRingCat.of A)) := Over.mk (𝟙 _)
  let a : (Over.map (algebraBaseMap M.ring A)).obj T ≅
      Over.mk s :=
    Over.isoMk (Iso.refl _) (by simp [T, hs])
  let φ := pullbackPointHom (algebraBaseMap M.ring A) q e T
  have hf (z : Over.mk s ⟶
      N.X ⊗ ((splitTorus M.base M.coordinates).X ⊗ U.X)) :
      φ ((a.hom ≫ z) ≫ Dynamic.tripleCellMultiplication iN M.inclusion iU) =
        (a.hom ≫ z) ≫ snd _ _ ≫ fst _ _ ≫ p.hom.hom :=
    pullbackPointHom_tripleCell _ q e T χ iN M.inclusion iU hN hU p hq' (a.hom ≫ z)
  apply (cancel_epi a.hom).mp
  have hxy' := congrArg φ (congrArg (a.hom ≫ ·) hxy)
  simp only [MonObj.comp_mul, ← Category.assoc, map_mul] at hxy'
  rw [hf x, hf y, hf c] at hxy'
  simpa only [MonObj.comp_mul, Category.assoc] using hxy'

/-- The compatible canonical cell gives a smooth surjective actual coroot
quotient over every coefficient ring. -/
theorem exists_smooth_corootQuotient_of_local
    (hlocal : RelativeDerivedLocalCorootQuotientExistenceStatement.{u})
    (M : AffinePinnedModel.{u}) [DecidableEq M.coordinates] :
    ∃ q : M.group ⟶ (corootQuotient (CommRingCat.of M.ring) M.rootDatum).toGrp,
      M.inclusion ≫ q = corootProjection (CommRingCat.of M.ring) M.rootDatum ∧
      Smooth q.hom.hom.left ∧ Surjective q.hom.hom.left := by
  let : Smooth M.group.X.hom := M.reductive.smooth
  let : IsAffineHom M.group.X.hom := M.reductive.isAffineHom
  let : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom
  let : GeometricallyIrreducible M.group.X.hom := M.reductive.geometricallyIrreducible
  let : IsClosedImmersion M.inclusion.hom.hom.left := M.closed
  let : Mono M.inclusion.hom.hom := Over.mono_of_mono_left _
  let χ := BasedBorelTransport.cocharacter M.inclusion M.rootDatum M.basis
  let χn := CommGroupScheme.groupHom (Gm.powerHom M.base (-1)) ≫ χ
  let N := Dynamic.Affine.unipotentScheme χn
  let U := Dynamic.Affine.unipotentScheme χ
  let L := splitTorus M.base M.coordinates
  let iN : N ⟶ M.group := Dynamic.Affine.unipotentHom χn
  let iU : U ⟶ M.group := Dynamic.Affine.unipotentHom χ
  have hN : (Dynamic.unipotent χn).IsRepresentedBy iN :=
    Dynamic.Affine.isRepresentedBy_unipotentHom χn
  have hU : (Dynamic.unipotent χ).IsRepresentedBy iU :=
    Dynamic.Affine.isRepresentedBy_unipotentHom χ
  have hL : (Dynamic.centralizer χ).IsRepresentedBy M.inclusion :=
    ⟨inferInstance, M.centralizer_originalCocharacter.symm⟩
  let C := N.X ⊗ (L.X ⊗ U.X)
  let j : C ⟶ M.group.X := Dynamic.tripleCellMultiplication iN M.inclusion iU
  let p := corootProjection (CommRingCat.of M.ring) M.rootDatum
  let ν : C ⟶ (corootQuotient (CommRingCat.of M.ring) M.rootDatum).X :=
    snd N.X (L.X ⊗ U.X) ≫ fst L.X U.X ≫ p.hom.hom
  let : IsOpenImmersion j.left :=
    Dynamic.isOpenImmersion_tripleCellMultiplication_overBase χ hN hL hU
  have hc : CellGluing.CellCompatible j ν :=
    cellCompatible_dynamic_of_localCorootQuotient hlocal M iN iU hN hU
  let e : 𝟙_ (Over M.base) ⟶ C := lift 1 (lift 1 1)
  have he : e ≫ j = 1 := by
    simp only [e, j, Dynamic.lift_tripleCellMultiplication, MonObj.one_comp, one_mul]
  let q := CellGluing.glueHom hc e he
  have hcell : j ≫ q.hom.hom = ν := CellGluing.cell_comp_glueHom hc e he
  let t : L.X ⟶ C := lift 1 (lift (𝟙 _) 1)
  have htj : t ≫ j = M.inclusion.hom.hom := by
    simp only [t, j, Dynamic.lift_tripleCellMultiplication, MonObj.one_comp,
      Category.id_comp, one_mul, mul_one]
  have htν : t ≫ ν = p.hom.hom := by
    simp only [t, ν, lift_snd_assoc, lift_fst_assoc, Category.id_comp]
  have hrestrict : M.inclusion ≫ q = p := by
    apply Grp.hom_ext
    rw [Grp.comp_hom_hom, ← htj, Category.assoc, hcell, htν]
  let : Smooth N.X.hom :=
    ((dynamicBaseSmoothConnected M.base M.group χn N iN).1 hN).1
  let : Smooth U.X.hom :=
    ((dynamicBaseSmoothConnected M.base M.group χ U iU).1 hU).1
  let : Smooth (snd N.X (L.X ⊗ U.X)).left :=
    inferInstanceAs (Smooth (pullback.snd N.X.hom (L.X ⊗ U.X).hom))
  let : Smooth (fst L.X U.X).left :=
    inferInstanceAs (Smooth (pullback.fst L.X.hom U.X.hom))
  let : Smooth p.hom.hom.left := smooth_corootProjection (CommRingCat.of M.ring) M.rootDatum
  let : Smooth ν.left := by
    change Smooth ((snd N.X (L.X ⊗ U.X)).left ≫
      (fst L.X U.X).left ≫ p.hom.hom.left)
    infer_instance
  let : Smooth (corootQuotient (CommRingCat.of M.ring) M.rootDatum).X.hom :=
    (isSplitTorus_corootQuotient (CommRingCat.of M.ring) M.rootDatum).smooth
  have hqsmooth : Smooth q.hom.hom.left := by
    let : Smooth (j ≫ q.hom.hom).left := by rw [hcell]; infer_instance
    exact smooth_of_smooth_openCell M.reductive q j e he
  have hqsurj : Surjective q.hom.hom.left := by
    have h : Surjective (M.inclusion.hom.hom.left ≫ q.hom.hom.left) := by
      change Surjective (M.inclusion ≫ q).hom.hom.left
      rw [hrestrict]
      exact surjective_corootProjection (CommRingCat.of M.ring) M.rootDatum
    exact Surjective.of_comp M.inclusion.hom.hom.left q.hom.hom.left
  exact ⟨q, hrestrict, hqsmooth, hqsurj⟩

end RelativeDerived

/-- The local coefficient-ring quotient problem implies the split relative
torus-quotient problem, including semisimplicity of every full geometric kernel. -/
theorem relativeDerivedSplitTorusQuotient_of_localCorootQuotient
    (hlocal : RelativeDerivedLocalCorootQuotientExistenceStatement.{u}) :
    RelativeDerivedSplitTorusQuotientExistenceStatement.{u} := by
  intro M
  classical
  obtain ⟨q, hq, hsmooth, hsurj⟩ :=
    RelativeDerived.exists_smooth_corootQuotient_of_local hlocal M
  exact ⟨_, q, RelativeDerived.isTorus_corootQuotient _ _, hsmooth, hsurj,
    RelativeDerived.isSemisimple_corootQuotient_geometricKernel M q hq⟩

/-- Global existence follows from the local coefficient-ring construction and
the separate relative semisimple perfectness input. -/
theorem relativeDerivedGroupExistence_of_localCorootQuotient
    (hperf : RelativeSemisimpleFppfPerfectStatement.{u})
    (hlocal : RelativeDerivedLocalCorootQuotientExistenceStatement.{u}) :
    RelativeDerivedGroupExistenceStatement.{u} :=
  relativeDerivedGroupExistence_of_splitTorusQuotient hperf
    (relativeDerivedSplitTorusQuotient_of_localCorootQuotient hlocal)

end Langlands.GroupScheme
