import Langlands.GroupScheme.Rational.LeviCocenterRootModelAssembly
import Langlands.GroupScheme.Rational.LeviCocenterRootModelStatement
import Langlands.GroupScheme.Rational.StandardLeviStandardFamiliesProof
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Derived.CocenterQuotientProof
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent
import Langlands.GroupScheme.Derived.MaximalTorusProductSurjectivityProof
import Langlands.GroupScheme.Derived.MaximalTorusIntersectionProof
import Langlands.GroupScheme.Derived.SemisimpleProof
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.FieldSeparatedProof
import Langlands.GroupScheme.Rational.SplitTorus

/-! # Cocenter characters of the centralizer of a cocharacter

Let `amb : T ⟶ G` be a maximal torus of a connected reductive group over `k`,
split over an extension `E` with root datum `P` there, and let `L` be the
centralizer of a cocharacter `ζ` of `T`, with an fppf quotient `r : L ⟶ R` by
its derived subgroup. Over `E` the cocenter `R` is split, and pulling back
characters along `T ⟶ L ⟶ R` identifies the characters of `R` with the
characters of `T` annihilating the coroots of the roots vanishing on `ζ`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.DynamicCentralizerCocenterComparison

local instance baseChangeAffine
    {k K : Type u} [Field k] [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom H.X.hom] :
    IsAffineHom ((GroupScheme.baseChange b).obj H).X.hom :=
  MorphismProperty.baseChange_obj (P := @IsAffineHom) b H.X inferInstance

local instance baseChangeFiniteType
    {k K : Type u} [Field k] [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (H : GroupScheme (Spec (CommRingCat.of k))) [LocallyOfFiniteType H.X.hom] :
    LocallyOfFiniteType ((GroupScheme.baseChange b).obj H).X.hom :=
  MorphismProperty.baseChange_obj (P := @LocallyOfFiniteType) b H.X inferInstance

/-- The representing inclusion of the dynamic centralizer of a cocharacter of an
affine group is a closed subgroup. -/
theorem isClosedSubgroup {k : Type u} [Field k]
    {G L : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (amb : T.toGrp ⟶ G) (ζ : cocharacterLattice T) (l : L ⟶ G)
    (hl : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ amb)).IsRepresentedBy l) :
    IsClosedSubgroup l := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  rw [← hl.isoOfIsRepresentedBy_hom_comp
    (Dynamic.Affine.isRepresentedBy_centralizerHom (CommGroupScheme.groupHom ζ ≫ amb))]
  exact IsClosedSubgroup.iso_comp _ (Dynamic.Affine.isClosedSubgroup_centralizerHom _)

/-- Any fppf quotient of a connected reductive group by its derived subgroup
splits over a field splitting one of its maximal tori. -/
theorem cocenter_isSplitTorus {k : Type u} [Field k] (E : Type u) [Field E] [Algebra k E]
    {L D : GroupScheme (Spec (CommRingCat.of k))} (hL : IsConnectedReductive L)
    {T R : CommGroupScheme (Spec (CommRingCat.of k))} {tL : T.toGrp ⟶ L}
    (htL : IsMaximalTorus tL)
    (hTE : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T).toGrp)
    {e : D ⟶ L} (he : IsDerivedSubgroup e)
    {r : L ⟶ R.toGrp} (hr : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range e) r) :
    IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj R).toGrp := by
  let : IsAffineHom L.X.hom := hL.isAffineHom
  obtain ⟨R₀, r₀, -, hr₀, -, hmax⟩ := cocenterQuotientExistence k L D e hL he
  have hR₀E : IsSplitTorus ((GroupScheme.baseChange (algebraBaseMap k E)).obj R₀.toGrp) :=
    (hmax T tL htL E hTE).1
  let : IsSeparated R.toGrp.X.hom := fieldSeparated k R.toGrp
  let : IsSeparated R₀.toGrp.X.hom := fieldSeparated k R₀.toGrp
  let : QuasiCompact r.hom.hom.left := by
    have : QuasiCompact (r.hom.hom.left ≫ R.toGrp.X.hom) := by
      rw [Over.w r.hom.hom]
      infer_instance
    exact QuasiCompact.of_comp _ R.toGrp.X.hom
  let : QuasiCompact r₀.hom.hom.left := by
    have : QuasiCompact (r₀.hom.hom.left ≫ R₀.toGrp.X.hom) := by
      rw [Over.w r₀.hom.hom]
      infer_instance
    exact QuasiCompact.of_comp _ R₀.toGrp.X.hom
  exact IsSplitTorus.of_iso
    ((GroupScheme.baseChange (algebraBaseMap k E)).mapIso (FppfQuotientComparison.iso hr hr₀)) hR₀E

/-- **Split cocenter comparison.** Over a field where the maximal torus `T`
and the cocenter `R` of the centralizer `L` of `ζ` are split, the characters of
`R` pulled back to `T` are injectively the characters annihilating the coroots
of the roots vanishing on `ζ`. -/
theorem splitComparison {K : Type u} [Field K]
    {G L D : GroupScheme (Spec (CommRingCat.of K))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom L.X.hom] [LocallyOfFiniteType L.X.hom]
    {T R : CommGroupScheme (Spec (CommRingCat.of K))}
    {amb : T.toGrp ⟶ G} (hamb : IsClosedSubgroup amb)
    (hT : IsSplitTorus T.toGrp) (hR : IsSplitTorus R.toGrp)
    {J : Type v} {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf amb P)
    (ζ : cocharacterLattice T) (l : L ⟶ G)
    (hl : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ amb)).IsRepresentedBy l)
    (hL : IsConnectedReductive L)
    (tL : T.toGrp ⟶ L) (htL : tL ≫ l = amb) (htLm : IsMaximalTorus tL)
    (e : D ⟶ L) (he : IsDerivedSubgroup e)
    (r : L ⟶ R.toGrp) (hr : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range e) r) :
    Function.Injective (characterLattice.precompose (Additive.ofMul (tL ≫ r) : T ⟶ R)) ∧
      ∀ χ, χ ∈ (characterLattice.precompose
          (Additive.ofMul (tL ≫ r) : T ⟶ R)).toIntLinearMap.range ↔
        ∀ p, P.root' p ζ = 0 → P.toLinearMap χ (P.coroot p) = 0 := by
  obtain ⟨JL, -, PL, hPL, -⟩ := rootDatumExistence K L hL T hT tL htLm
  have hroots := relativeRoots_centralizer_factor dynamicLie amb tL l htL ζ hl
  exact characterLattice.cocenter_coweight_comparison_of_structuralInputs
    rootDatumExistence derivedSubgroupSemisimple derivedMaximalTorusProductSurjectivity
    derivedMaximalTorusIntersection hP hPL l htL hL e he htLm hamb r hr hT hR ζ hroots

/-- **Cocenter comparison for a cocharacter centralizer.** Over an algebraic
field extension `E` splitting the maximal torus `T`, the cocenter `R` of the
centralizer `L` of `ζ` is split, and the characters of `R` pulled back to `T`
are injectively the characters annihilating the coroots of the roots vanishing
on `ζ`. -/
theorem comparison {k : Type u} [Field k] (E : Type u) [Field E] [Algebra k E]
    [Algebra.IsAlgebraic k E]
    {G L D : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {T R : CommGroupScheme (Spec (CommRingCat.of k))}
    {amb : T.toGrp ⟶ G} (hamb : IsMaximalTorus amb)
    (hTE : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T).toGrp)
    {J : Type v}
    {P : RootDatum J
      (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))
      (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))}
    (hP : IsRootDatumOf ((GroupScheme.baseChange (algebraBaseMap k E)).map amb) P)
    (ζ : cocharacterLattice T) (l : L ⟶ G)
    (hl : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ amb)).IsRepresentedBy l)
    (tL : T.toGrp ⟶ L) (htL : tL ≫ l = amb)
    (e : D ⟶ L) (he : IsDerivedSubgroup e)
    (r : L ⟶ R.toGrp) (hr : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range e) r) :
    IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj R).toGrp ∧
      Function.Injective
        (characterLattice.baseChangePullback k E (Additive.ofMul (tL ≫ r) : T ⟶ R)) ∧
      ∀ χ, χ ∈ (characterLattice.baseChangePullback k E
          (Additive.ofMul (tL ≫ r) : T ⟶ R)).range ↔
        ∀ p, P.root' p (cocharacterLattice.baseChange (algebraBaseMap k E) T ζ) = 0 →
          P.toLinearMap χ (P.coroot p) = 0 := by
  let b := algebraBaseMap k E
  let F := GroupScheme.baseChange b
  have hlc : IsClosedSubgroup l := isClosedSubgroup amb ζ l hl
  have hL : IsConnectedReductive L := dynamicCentralizerReductive k G hG _ L l hlc hl
  have : IsAffineHom L.X.hom := hL.isAffineHom
  have : Smooth L.X.hom := hL.smooth
  have : LocallyOfFiniteType L.X.hom := inferInstance
  have htLm : IsMaximalTorus tL := IsMaximalTorus.of_comp hlc (by rwa [htL])
  have hRE := cocenter_isSplitTorus E hL htLm hTE he hr
  have hLE : IsConnectedReductive (F.obj L) := hL.baseChange_of_algebraicExtension
  have htLE : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj T) (F.map tL) :=
    (maximalTorusBaseChange k E L T tL htLm.1 htLm.2.1).1 htLm
  have heE : IsDerivedSubgroup (F.map e) :=
    he.baseChange_of_eq b (derivedSubgroup_baseChange_eq_of_field b L)
  have hrE : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (F.map e)) (F.map r) := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hr.baseChange b
  have hlE : (Dynamic.centralizer (CommGroupScheme.groupHom
      (cocharacterLattice.baseChange b T ζ) ≫ F.map amb)).IsRepresentedBy (F.map l) := by
    rw [cocharacterLattice.groupHom_baseChange_dynamic, ← Dynamic.baseChangeCocharacter_comp]
    exact Dynamic.isRepresentedBy_centralizer_baseChange b _ hl
  have hcompE : F.map tL ≫ F.map l = F.map amb := by rw [← Functor.map_comp, htL]
  have hc := splitComparison (hamb.2.1.baseChange b) hTE hRE hP
    (cocharacterLattice.baseChange b T ζ) (F.map l) hlE hLE (F.map tL) hcompE htLE
    (F.map e) heE (F.map r) hrE
  have hmap :
      (CommGroupScheme.baseChange b).map (Additive.ofMul (tL ≫ r) : T ⟶ R) =
        (Additive.ofMul (F.map tL ≫ F.map r) :
          (CommGroupScheme.baseChange b).obj T ⟶ (CommGroupScheme.baseChange b).obj R) := by
    change Additive.ofMul (F.map (tL ≫ r)) = _
    rw [Functor.map_comp]
    rfl
  refine ⟨hRE, ?_, fun χ => ?_⟩
  · change Function.Injective (characterLattice.precompose
      ((CommGroupScheme.baseChange b).map (Additive.ofMul (tL ≫ r) : T ⟶ R)))
    rw [hmap]
    exact hc.1
  · change χ ∈ (characterLattice.precompose
      ((CommGroupScheme.baseChange b).map
        (Additive.ofMul (tL ≫ r) : T ⟶ R))).toIntLinearMap.range ↔ _
    rw [hmap]
    exact hc.2 χ

end Langlands.GroupScheme.DynamicCentralizerCocenterComparison
