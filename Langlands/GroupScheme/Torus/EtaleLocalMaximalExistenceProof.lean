import Langlands.GroupScheme.Torus.EtaleLocalMaximalExistenceStatement
import Langlands.GroupScheme.Torus.FibrewiseMaximalTransport
import Langlands.GroupScheme.Torus.RelativeLiftingProof
import Langlands.GroupScheme.Reductive.TorusLiftingOpenConstruction
import Langlands.GroupScheme.Reductive.BaseChange

/-! # Maximal tori exist étale-locally on an arbitrary base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

local instance etaleMaximal_smooth_pullback {S U : Scheme.{u}} (G : GroupScheme S)
    [Smooth G.X.hom] (b : U ⟶ S) : Smooth ((baseChange b).obj G).X.hom :=
  inferInstanceAs (Smooth (Limits.pullback.snd G.X.hom b))

local instance etaleMaximal_affine_pullback {S U : Scheme.{u}} (G : GroupScheme S)
    [IsAffineHom G.X.hom] (b : U ⟶ S) : IsAffineHom ((baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

namespace splitTorus

/-- A closed standard torus maximal at a field point of an affine base is
fibrewise maximal on an affine open neighbourhood of that point. -/
theorem exists_affine_open_fibrewiseMaximal_of_fieldPoint
    {r : Type u} [CommRing r] (I : Type u) [Fintype I]
    (G : GroupScheme (Spec (CommRingCat.of r))) (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G) (hi : IsClosedSubgroup i)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of r))
    (hmax : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj
      (commGroupScheme _ I)) ((baseChange b).map i)) :
    ∃ (A : CommRingCat.{u}) (a : Spec A ⟶ Spec (CommRingCat.of r)),
      IsOpenImmersion a ∧ b (IsLocalRing.closedPoint k) ∈ Set.range a ∧
      ∃ (j : splitTorus (Spec A) I ⟶ (baseChange a).obj G),
        IsClosedSubgroup j ∧ IsFibrewiseMaximalTorus (T := commGroupScheme _ I) j := by
  classical
  let := hG.smooth
  let := hG.isAffineHom
  have hm := isMaximalTorus_residueFibre_of_fieldPoint hi b hmax
  have hs := mem_geometricSelfCentralizingTorusLocus_of_geometricFiberHom I G i hG hi _
    (isMaximalTorus_geometricFiberHom_of_residueFibre I G i _ hm)
  let V : (Spec (CommRingCat.of r)).Opens :=
    ⟨geometricSelfCentralizingTorusLocus I G i,
      isOpen_geometricSelfCentralizingTorusLocus I G i hi⟩
  obtain ⟨A, a, ha, hb, hV⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (U := V) hs
  let j : splitTorus (Spec A) I ⟶ (baseChange a).obj G :=
    (baseChangeIso a I).inv ≫ (baseChange a).map i
  refine ⟨A, a, ha, hb, j, (hi.baseChange a).iso_comp (baseChangeIso a I).symm, ?_⟩
  intro x
  have hx := isMaximalTorus_residueFibre_of_geometricFiberHom I G i hi (a x)
    (isMaximalTorus_geometricFiberHom_of_mem I G i hG hi (a x) (hV ⟨x, rfl⟩))
  let c := (Spec A).fromSpecResidueField x
  have hcx : (c ≫ a) (IsLocalRing.closedPoint ((Spec A).residueField x)) = a x := by
    change a (c _) = a x
    rw [Scheme.fromSpecResidueField_apply]
  have hc := isMaximalTorus_fieldPoint_of_residueFibre
    (T := commGroupScheme _ I) (i := i) (k := (Spec A).residueField x) (c ≫ a)
    (by erw [hcx]; exact hx)
  exact isMaximalTorus_baseChangedHom_comp I G i a
    (k := (Spec A).residueField x) c hc

/-- A closed standard torus maximal at a field point of any base is
fibrewise maximal on an affine open neighbourhood of that point. -/
theorem exists_affine_open_fibrewiseMaximal_of_fieldPoint_overScheme
    {S : Scheme.{u}} (I : Type u) [Fintype I]
    (G : GroupScheme S) (hG : IsReductive G)
    (i : splitTorus S I ⟶ G) (hi : IsClosedSubgroup i)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (hmax : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj
      (commGroupScheme S I)) ((baseChange b).map i)) :
    ∃ (A : CommRingCat.{u}) (a : Spec A ⟶ S),
      IsOpenImmersion a ∧ b (IsLocalRing.closedPoint k) ∈ Set.range a ∧
      ∃ (j : splitTorus (Spec A) I ⟶ (baseChange a).obj G),
        IsClosedSubgroup j ∧ IsFibrewiseMaximalTorus (T := commGroupScheme _ I) j := by
  classical
  let l := S.affineOpenCover.idx (b (IsLocalRing.closedPoint k))
  let A := S.affineOpenCover.X l
  let a : Spec A ⟶ S := S.affineOpenCover.f l
  have hrange : Set.range b ⊆ Set.range a := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z (IsLocalRing.closedPoint k)]
    exact S.affineOpenCover.covers (b (IsLocalRing.closedPoint k))
  let c : Spec (CommRingCat.of k) ⟶ Spec A := IsOpenImmersion.lift a b hrange
  have hc : c ≫ a = b := IsOpenImmersion.lift_fac a b hrange
  let H := (baseChange a).obj G
  let iA : splitTorus (Spec A) I ⟶ H := (baseChangeIso a I).inv ≫ (baseChange a).map i
  have hiA : IsClosedSubgroup iA :=
    (hi.baseChange a).iso_comp (baseChangeIso a I).symm
  have hm : IsMaximalTorus (T := (CommGroupScheme.baseChange c).obj
      (commGroupScheme (Spec A) I)) ((baseChange c).map iA) :=
    isMaximalTorus_baseChangedHom_comp I G i a c (by rw [hc]; exact hmax)
  obtain ⟨B, v, hv, hx, j, hj, hmj⟩ :=
    exists_affine_open_fibrewiseMaximal_of_fieldPoint I H (hG.baseChange a) iA hiA c hm
  let : IsOpenImmersion v := hv
  let ε := (baseChangeCompIso a v G).symm
  refine ⟨B, v ≫ a, inferInstance, ?_, j ≫ ε.hom, hj.comp_iso ε, hmj.comp_iso ε⟩
  obtain ⟨x, hx⟩ := hx
  refine ⟨x, ?_⟩
  calc
    (v ≫ a) x = a (c (IsLocalRing.closedPoint k)) := congrArg a hx
    _ = b (IsLocalRing.closedPoint k) := congrArg (fun f => f (IsLocalRing.closedPoint k)) hc

end splitTorus

set_option maxHeartbeats 4000000 in
/-- Every point of the base has an affine étale neighbourhood carrying a
closed standard split torus maximal on every residue fibre. -/
theorem exists_etale_affine_split_maximalTorus
    (S : Scheme.{u}) (G : GroupScheme S) (hG : IsReductive G) (s : S) :
    ∃ (R : Type u) (_ : CommRing R) (f : Spec (CommRingCat.of R) ⟶ S),
      Etale f ∧ (∃ x, f x = s) ∧
      ∃ (I : Type u) (_ : Fintype I)
        (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ (baseChange f).obj G),
        IsClosedSubgroup i ∧
          IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i := by
  classical
  let := hG.smooth
  let := hG.isAffineHom
  obtain ⟨K, hK, aK, hfin, hgal, T₀, i₀, hT₀, hmax₀⟩ :=
    exists_finiteGalois_hasSplitMaximalTorus torusFiniteGaloisSplitting
      maximalTorusBaseChange ((baseChange (S.fromSpecResidueField s)).obj G)
  let : Field K := hK
  let : Algebra (S.residueField s) K := aK
  let : FiniteDimensional (S.residueField s) K := hfin
  let : IsGalois (S.residueField s) K := hgal
  let d := Langlands.AlgebraicGeometry.etaleResidueExtension S s K
  let : Etale d.projection := d.etale
  let q := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K))
  let ε₀ := baseChangeCompIso (S.fromSpecResidueField s) q G
  let j₀ : T₀.toGrp ⟶ (baseChange d.extensionPoint).obj G := i₀ ≫ ε₀.inv
  have hm₀ : IsMaximalTorus (T := T₀) j₀ := hmax₀.comp_iso ε₀.symm
  let TC := (CommGroupScheme.baseChange d.inverseResiduePoint).obj T₀
  let jC := d.torusFibreInclusion G T₀.toGrp j₀
  have hTC : IsSplitTorus TC.toGrp := d.torusFibre_isSplit T₀.toGrp hT₀
  have hmC : IsMaximalTorus (T := TC) jC :=
    d.torusFibreInclusion_isMaximal G T₀ j₀ hm₀
  let H := (baseChange d.projection).obj G
  obtain ⟨U, p, hp, b, hb, T, hT, i, hi, e, he⟩ :=
    relativeSplitTorusLifting d.neighbourhood H d.point TC.toGrp hTC jC hmC.2.1
  let : Etale p := hp
  let TL : CommGroupScheme U := { T with comm := hT.isCommMonObj }
  have hm : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj TL)
      ((baseChange b).map i) :=
    isMaximalTorus_of_lifting_recovery H d.point p b hb TL TC i jC e he hmC
  obtain ⟨I, hI, ⟨eI⟩⟩ := hT
  let : Fintype I := Fintype.ofFinite I
  let j : splitTorus U I ⟶ (baseChange p).obj H := eI.inv ≫ i
  have hj : IsClosedSubgroup j := (show IsClosedSubgroup i from hi).iso_comp eI.symm
  have hmj : IsMaximalTorus
      (T := (CommGroupScheme.baseChange b).obj (splitTorus.commGroupScheme U I))
      ((baseChange b).map j) :=
    (isMaximalTorus_baseChange_inv_comp_iff
      (k := d.neighbourhood.residueField d.point) b (T := TL)
      (T' := splitTorus.commGroupScheme U I) eI i).mpr hm
  obtain ⟨A, a, ha, hpoint, t, ht, hmt⟩ :=
    splitTorus.exists_affine_open_fibrewiseMaximal_of_fieldPoint_overScheme I
      ((baseChange p).obj H) ((hG.baseChange d.projection).baseChange p) j hj b hmj
  let : IsOpenImmersion a := ha
  let f := (a ≫ p) ≫ d.projection
  let ε : (baseChange a).obj ((baseChange p).obj H) ≅ (baseChange f).obj G :=
    (baseChangeCompIso p a H).symm ≪≫
      (baseChangeCompIso d.projection (a ≫ p) G).symm
  have hbpoint : p (b (IsLocalRing.closedPoint (d.neighbourhood.residueField d.point))) =
      d.point := by
    calc
      _ = d.neighbourhood.fromSpecResidueField d.point
          (IsLocalRing.closedPoint (d.neighbourhood.residueField d.point)) :=
        congrArg (fun f => f (IsLocalRing.closedPoint
          (d.neighbourhood.residueField d.point))) hb
      _ = d.point := Scheme.fromSpecResidueField_apply _ _
  refine ⟨A, inferInstance, f, inferInstance, ?_, I, inferInstance,
    t ≫ ε.hom, ht.comp_iso ε, hmt.comp_iso ε⟩
  obtain ⟨x, hx⟩ := hpoint
  refine ⟨x, ?_⟩
  change d.projection (p (a x)) = s
  rw [hx]
  erw [hbpoint, d.point_over]

/-- Reductive group schemes admit maximal tori étale-locally on every base. -/
theorem etaleLocalMaximalTorusExistence :
    EtaleLocalMaximalTorusExistenceStatement.{u} := by
  classical
  intro S G hG
  choose R hR f hf hx I hI i hi hmax using exists_etale_affine_split_maximalTorus S G hG
  let 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S :=
    Scheme.Cover.mkOfCovers (P := @Etale) S (fun s => Spec (CommRingCat.of (R s))) f
      (fun s => ⟨s, hx s⟩) hf
  refine ⟨𝒰, fun s => ⟨splitTorus.commGroupScheme _ (I s), i s, ?_, hi s, hmax s⟩⟩
  exact RelativeTorus.IsTorus.of_isSplitTorus (isSplitTorus_splitTorus (I s))

end Langlands.GroupScheme
