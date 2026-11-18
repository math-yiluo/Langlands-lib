import Langlands.GroupScheme.Rational.StandardLeviFamilyRestriction
import Langlands.GroupScheme.Rational.RelativeRankProof
import Langlands.GroupScheme.Rational.SemigroupTransport
import Langlands.GroupScheme.Rational.StandardParabolicOrderReduction
import Langlands.Geometry.Building.SpecialCompactLevi
import Langlands.BruhatTits.SpecialCompact.LeviApartmentComparison
import Langlands.Representation.Aubert.General.RationalPointFamily
import Langlands.Representation.Aubert.General.DynamicLeviTopology

/-! # Nested standard Levis: rank drop, simple-root labels and nested transports

Structural glue for a rank induction over the actual standard Levis of a connected
reductive group. The results are short corollaries of published Library theorems.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.StandardLeviNested

/-! ## Nested represented subgroups -/

section Represented

variable {S : Scheme.{u}} {L G H H' : GroupScheme S} {j : L ⟶ G}
  {F : SubgroupFunctor G} {E : SubgroupFunctor L} {h : H ⟶ L} {h' : H' ⟶ G}

/-- If `F` lies in the range of a monomorphism `j : L ⟶ G` and `h : H ⟶ L` represents
the preimage `E = j⁻¹ F`, then `h ≫ j` represents `F`. -/
theorem isRepresentedBy_comp (hj : Mono j.hom.hom) (hEF : F.comap j = E)
    (hE : E.IsRepresentedBy h) (hle : F ≤ SubgroupFunctor.range j) :
    F.IsRepresentedBy (h ≫ j) := by
  have hc := hE.comp (⟨hj, rfl⟩ : (SubgroupFunctor.range j).IsRepresentedBy j)
  rwa [← hEF, SubgroupFunctor.map_comap_of_le_range F hle] at hc

/-- The nested representative `H` of `j⁻¹ F` is isomorphic to any representative `H'`
of `F`. -/
def nestedIso (hj : Mono j.hom.hom) (hEF : F.comap j = E) (hE : E.IsRepresentedBy h)
    (hle : F ≤ SubgroupFunctor.range j) (hF : F.IsRepresentedBy h') : H ≅ H' :=
  (isRepresentedBy_comp hj hEF hE hle).isoOfIsRepresentedBy hF

/-- The nested isomorphism lies over `G`. -/
theorem nestedIso_hom_comp (hj : Mono j.hom.hom) (hEF : F.comap j = E)
    (hE : E.IsRepresentedBy h) (hle : F ≤ SubgroupFunctor.range j)
    (hF : F.IsRepresentedBy h') :
    (nestedIso hj hEF hE hle hF).hom ≫ h' = h ≫ j :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end Represented

/-- The pinned identity-test point topology on affine schemes over `Spec R`. -/
local instance nestedRationalPointTopology {R : Type u} [CommRing R] [TopologicalSpace R]
    (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left] :
    TopologicalSpace (RationalPoint R X) :=
  rationalPointTopology R X

/-! ## Rational points of nested represented subgroups -/

section Points

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {L G H H' : GroupScheme (Spec (CommRingCat.of R))} [IsAffine L.X.left] [IsAffine G.X.left]
  [IsAffine H.X.left] [IsAffine H'.X.left]
  {j : L ⟶ G} {F : SubgroupFunctor G} {E : SubgroupFunctor L} {h : H ⟶ L} {h' : H' ⟶ G}

/-- A multiplicative homeomorphism between the rational points of the nested
representative and of the ambient representative. No continuity of the group
operations is claimed at this generality. -/
def nestedPointHomeomorph (hj : Mono j.hom.hom) (hjc : IsClosedSubgroup j)
    (hEF : F.comap j = E) (hE : E.IsRepresentedBy h) (hhc : IsClosedSubgroup h)
    (hle : F ≤ SubgroupFunctor.range j) (hF : F.IsRepresentedBy h')
    (hh'c : IsClosedSubgroup h') :
    RationalPoint R H.X ≃ₜ* RationalPoint R H'.X :=
  (rationalPointSubgroupHomeomorph R F (h ≫ j) (isRepresentedBy_comp hj hEF hE hle)
    (hhc.comp hjc)).trans (rationalPointSubgroupHomeomorph R F h' hF hh'c).symm

omit [IsAffine L.X.left] in
/-- Composing the image of `p` with the ambient representative gives `p ≫ h ≫ j`. -/
theorem nestedPointHomeomorph_apply_comp (hj : Mono j.hom.hom) (hjc : IsClosedSubgroup j)
    (hEF : F.comap j = E) (hE : E.IsRepresentedBy h) (hhc : IsClosedSubgroup h)
    (hle : F ≤ SubgroupFunctor.range j) (hF : F.IsRepresentedBy h')
    (hh'c : IsClosedSubgroup h') (p : RationalPoint R H.X) :
    nestedPointHomeomorph hj hjc hEF hE hhc hle hF hh'c p ≫ h'.hom.hom =
      p ≫ h.hom.hom ≫ j.hom.hom := by
  have hx := congrArg Subtype.val
    ((rationalPointSubgroupHomeomorph R F h' hF hh'c).apply_symm_apply
      (rationalPointSubgroupHomeomorph R F (h ≫ j) (isRepresentedBy_comp hj hEF hE hle)
        (hhc.comp hjc) p))
  rw [rationalPointSubgroupHomeomorph_apply_coe, rationalPointSubgroupHomeomorph_apply_coe] at hx
  refine hx.trans ?_
  rw [Grp.comp_hom_hom]

omit [IsAffine L.X.left] in
/-- On points, the homeomorphism is composition with the nested isomorphism. -/
theorem nestedPointHomeomorph_apply (hj : Mono j.hom.hom) (hjc : IsClosedSubgroup j)
    (hEF : F.comap j = E) (hE : E.IsRepresentedBy h) (hhc : IsClosedSubgroup h)
    (hle : F ≤ SubgroupFunctor.range j) (hF : F.IsRepresentedBy h')
    (hh'c : IsClosedSubgroup h') (p : RationalPoint R H.X) :
    nestedPointHomeomorph hj hjc hEF hE hhc hle hF hh'c p =
      p ≫ (nestedIso hj hEF hE hle hF).hom.hom.hom := by
  have hm : Mono h'.hom.hom := hF.1
  apply hm.right_cancellation
  rw [nestedPointHomeomorph_apply_comp, Category.assoc, ← Grp.comp_hom_hom _ h',
    nestedIso_hom_comp, Grp.comp_hom_hom]

omit [IsAffine H'.X.left] in
/-- The rational points of `j⁻¹ F` inside `L(R)` and of `F` inside `G(R)`, with their
subspace topologies, are identified by `x ↦ x ≫ j`. -/
def nestedCarrierHomeomorph (hj : Mono j.hom.hom) (hjc : IsClosedSubgroup j)
    (hEF : F.comap j = E) (hE : E.IsRepresentedBy h) (hhc : IsClosedSubgroup h)
    (hle : F ≤ SubgroupFunctor.range j) :
    E.carrier (Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≃ₜ*
      F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of R)))) :=
  (rationalPointSubgroupHomeomorph R E h hE hhc).symm.trans
    (rationalPointSubgroupHomeomorph R F (h ≫ j) (isRepresentedBy_comp hj hEF hE hle)
      (hhc.comp hjc))

omit [IsAffine H'.X.left] in
set_option linter.unusedSectionVars false in
/-- On carriers, the homeomorphism is composition with `j`. -/
@[simp] theorem nestedCarrierHomeomorph_apply_coe (hj : Mono j.hom.hom)
    (hjc : IsClosedSubgroup j) (hEF : F.comap j = E) (hE : E.IsRepresentedBy h)
    (hhc : IsClosedSubgroup h) (hle : F ≤ SubgroupFunctor.range j)
    (x : E.carrier (Over.mk (𝟙 (Spec (CommRingCat.of R))))) :
    ((nestedCarrierHomeomorph hj hjc hEF hE hhc hle x : F.carrier _) : RationalPoint R G.X) =
      (x : RationalPoint R L.X) ≫ j.hom.hom := by
  have hx := congrArg Subtype.val
    ((rationalPointSubgroupHomeomorph R E h hE hhc).apply_symm_apply x)
  rw [rationalPointSubgroupHomeomorph_apply_coe] at hx
  change (rationalPointSubgroupHomeomorph R E h hE hhc).symm x ≫ (h ≫ j).hom.hom = _
  rw [Grp.comp_hom_hom, ← Category.assoc, hx]

end Points

/-! ## Nested dynamic centralizers -/

/-- The actual affine dynamic centralizer is affine. -/
local instance nestedCentralizerAffine {R : Type u} [CommRing R]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffine G.X.left]
    (χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ G) :
    IsAffine (Dynamic.Affine.centralizerScheme χ).X.left :=
  have : IsClosedImmersion (Dynamic.Affine.centralizerHom χ).hom.hom.left :=
    Dynamic.Affine.isClosedSubgroup_centralizerHom χ
  isAffine_of_isAffineHom (Dynamic.Affine.centralizerHom χ).hom.hom.left

section DynamicCentralizer

variable {R : Type u} [CommRing R]
  {L G : GroupScheme (Spec (CommRingCat.of R))} [IsAffine L.X.left] [IsAffine G.X.left]
  (j : L ⟶ G) (χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ L)
  (χ' : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ G)

omit [IsAffine L.X.left] [IsAffine G.X.left] in
/-- For a monomorphism `j` with `χ ≫ j = χ'`, `j⁻¹ Z_G(χ') = Z_L(χ)`. -/
theorem comap_centralizer (hj : Mono j.hom.hom) (hχ : χ ≫ j = χ') :
    (Dynamic.centralizer χ').comap j = Dynamic.centralizer χ := by
  subst hχ
  exact (Dynamic.centralizer_eq_comap_of_mono χ j).symm

omit [IsAffine G.X.left] in
/-- If `Z_G(χ')` lies in the range of `j`, the centralizer of `χ` in `L`, followed by `j`,
represents `Z_G(χ')`. -/
theorem isRepresentedBy_nestedCentralizerHom (hj : Mono j.hom.hom) (hχ : χ ≫ j = χ')
    (hle : Dynamic.centralizer χ' ≤ SubgroupFunctor.range j) :
    (Dynamic.centralizer χ').IsRepresentedBy (Dynamic.Affine.centralizerHom χ ≫ j) :=
  isRepresentedBy_comp hj (comap_centralizer j χ χ' hj hχ)
    (Dynamic.Affine.isRepresentedBy_centralizerHom χ) hle

/-- The actual centralizer scheme of `χ` in `L` and of `χ'` in `G` are isomorphic. -/
def nestedCentralizerIso (hj : Mono j.hom.hom) (hχ : χ ≫ j = χ')
    (hle : Dynamic.centralizer χ' ≤ SubgroupFunctor.range j) :
    Dynamic.Affine.centralizerScheme χ ≅ Dynamic.Affine.centralizerScheme χ' :=
  nestedIso hj (comap_centralizer j χ χ' hj hχ)
    (Dynamic.Affine.isRepresentedBy_centralizerHom χ) hle
    (Dynamic.Affine.isRepresentedBy_centralizerHom χ')

theorem nestedCentralizerIso_hom_comp (hj : Mono j.hom.hom) (hχ : χ ≫ j = χ')
    (hle : Dynamic.centralizer χ' ≤ SubgroupFunctor.range j) :
    (nestedCentralizerIso j χ χ' hj hχ hle).hom ≫ Dynamic.Affine.centralizerHom χ' =
      Dynamic.Affine.centralizerHom χ ≫ j :=
  nestedIso_hom_comp _ _ _ _ _

variable [TopologicalSpace R]

/-- A multiplicative homeomorphism between the rational points of the two centralizer
schemes. -/
def nestedCentralizerPointHomeomorph (hj : Mono j.hom.hom) (hjc : IsClosedSubgroup j)
    (hχ : χ ≫ j = χ') (hle : Dynamic.centralizer χ' ≤ SubgroupFunctor.range j) :
    RationalPoint R (Dynamic.Affine.centralizerScheme χ).X ≃ₜ*
      RationalPoint R (Dynamic.Affine.centralizerScheme χ').X :=
  nestedPointHomeomorph hj hjc (comap_centralizer j χ χ' hj hχ)
    (Dynamic.Affine.isRepresentedBy_centralizerHom χ)
    (Dynamic.Affine.isClosedSubgroup_centralizerHom χ) hle
    (Dynamic.Affine.isRepresentedBy_centralizerHom χ')
    (Dynamic.Affine.isClosedSubgroup_centralizerHom χ')

theorem nestedCentralizerPointHomeomorph_apply (hj : Mono j.hom.hom)
    (hjc : IsClosedSubgroup j) (hχ : χ ≫ j = χ')
    (hle : Dynamic.centralizer χ' ≤ SubgroupFunctor.range j)
    (p : RationalPoint R (Dynamic.Affine.centralizerScheme χ).X) :
    nestedCentralizerPointHomeomorph j χ χ' hj hjc hχ hle p =
      p ≫ (nestedCentralizerIso j χ χ' hj hχ hle).hom.hom.hom :=
  nestedPointHomeomorph_apply _ _ _ _ _ _ _ _ p

/-- The literal Levi points `Z_L(χ)(R) ⊆ L(R)` and `Z_G(χ')(R) ⊆ G(R)`, with their
subspace topologies, are identified by `x ↦ x ≫ j`. -/
def nestedLeviHomeomorph (hj : Mono j.hom.hom) (hjc : IsClosedSubgroup j)
    (hχ : χ ≫ j = χ') (hle : Dynamic.centralizer χ' ≤ SubgroupFunctor.range j) :
    (Dynamic.centralizer χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≃ₜ*
      (Dynamic.centralizer χ').carrier (Over.mk (𝟙 (Spec (CommRingCat.of R)))) :=
  nestedCarrierHomeomorph (h := Dynamic.Affine.centralizerHom χ) hj hjc
    (comap_centralizer j χ χ' hj hχ) (Dynamic.Affine.isRepresentedBy_centralizerHom χ)
    (Dynamic.Affine.isClosedSubgroup_centralizerHom χ) hle

@[simp] theorem nestedLeviHomeomorph_apply_coe (hj : Mono j.hom.hom)
    (hjc : IsClosedSubgroup j) (hχ : χ ≫ j = χ')
    (hle : Dynamic.centralizer χ' ≤ SubgroupFunctor.range j)
    (x : (Dynamic.centralizer χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of R))))) :
    ((nestedLeviHomeomorph j χ χ' hj hjc hχ hle x :
        (Dynamic.centralizer χ').carrier _) : RationalPoint R G.X) =
      (x : RationalPoint R L.X) ≫ j.hom.hom :=
  nestedCarrierHomeomorph_apply_coe _ _ _ _ _ _ x

/-- The scheme-level and literal-Levi homeomorphisms are compatible with the published
point identifications `dynamicCentralizerPointHomeomorph`. -/
theorem dynamicCentralizerPointHomeomorph_nested (hj : Mono j.hom.hom)
    (hjc : IsClosedSubgroup j) (hχ : χ ≫ j = χ')
    (hle : Dynamic.centralizer χ' ≤ SubgroupFunctor.range j)
    (p : RationalPoint R (Dynamic.Affine.centralizerScheme χ).X) :
    Aubert.General.dynamicCentralizerPointHomeomorph R G χ'
        (nestedCentralizerPointHomeomorph j χ χ' hj hjc hχ hle p) =
      nestedLeviHomeomorph j χ χ' hj hjc hχ hle
        (Aubert.General.dynamicCentralizerPointHomeomorph R L χ p) := by
  apply Subtype.ext
  rw [nestedLeviHomeomorph_apply_coe, Aubert.General.dynamicCentralizerPointHomeomorph_apply_coe,
    Aubert.General.dynamicCentralizerPointHomeomorph_apply_coe]
  change nestedPointHomeomorph _ _ _ _ _ _ _ _ p ≫ _ = _
  rw [nestedPointHomeomorph_apply_comp, Category.assoc]

end DynamicCentralizer

/-! ## Actual standard Levis -/

/-- The actual standard Levi representative is affine over the base. -/
local instance nestedLeviSchemeAffineHom {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom_source

/-- An affine group scheme over a field is affine. -/
local instance nestedAmbientAffine {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

section Standard

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-! ### Rank drop -/

/-- Structural package for the actual standard Levi `M_J`, with
`iL = Standard.leviTorusHom i ν J`: `M_J` is connected reductive, `iL` is maximal split,
`ν` is generic for `iL`, the simple roots of `iL` are exactly `J`, `J` is finite,
the relative rank of `iL` is `Nat.card J`, and for `K ⊆ J` the standard parabolic, Levi
and unipotent subgroup functors of `iL` are the preimages of those of `i`. -/
theorem leviScheme_rankPackage (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) (J : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    IsConnectedReductive (Standard.leviScheme i ν J) ∧
      IsMaximalSplitTorus (Standard.leviTorusHom i ν J) ∧
      IsGenericCocharacter (Standard.leviTorusHom i ν J) ν ∧
      simpleRelativeRoots (Standard.leviTorusHom i ν J) ν = J ∧
      J.Finite ∧
      relativeRootRank (Standard.leviTorusHom i ν J) = Nat.card J ∧
      ∀ K : Set (characterLattice T), K ⊆ J →
        standardParabolic (Standard.leviTorusHom i ν J) ν K =
            (standardParabolic i ν K).comap (Standard.leviHom i ν J) ∧
          standardLevi (Standard.leviTorusHom i ν J) ν K =
            (standardLevi i ν K).comap (Standard.leviHom i ν J) ∧
          standardUnipotent (Standard.leviTorusHom i ν J) ν K =
            (standardUnipotent i ν K).comap (Standard.leviHom i ν J) := by
  have hL := BruhatTits.SpecialCompact.standardLevi_isConnectedReductive hG i hi ν hν J hJ
  have hiL : IsMaximalSplitTorus (Standard.leviTorusHom i ν J) :=
    Standard.isMaximalSplitTorus_leviTorusHom i ν J hi
  obtain ⟨hsimple, hνL, hfam⟩ :=
    standardLeviStandardFamilies dynamicLie standardCocharacter k G hG T i hi ν hν J hJ
      (Standard.leviScheme i ν J) hL (Standard.leviHom i ν J)
      (Standard.isRepresentedBy_leviHom i ν J) (Standard.isClosedSubgroup_leviHom i ν J)
  have hsimple' : simpleRelativeRoots (Standard.leviTorusHom i ν J) ν = J := hsimple
  obtain ⟨hfin, -, hrank⟩ :=
    relativeSimpleRootBasis k (Standard.leviScheme i ν J) hL T
      (Standard.leviTorusHom i ν J) hiL ν hνL
  refine ⟨hL, hiL, hνL, hsimple', ?_, ?_, hfam⟩
  · rw [← hsimple']; exact Set.toFinite _
  · rw [hrank, hsimple']

/-- The simple roots of `Standard.leviTorusHom i ν J` are exactly `J`. -/
theorem simpleRelativeRoots_leviTorusHom (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) (J : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    simpleRelativeRoots (Standard.leviTorusHom i ν J) ν = J :=
  (leviScheme_rankPackage hG i hi ν hν J hJ).2.2.2.1

/-- **Strict rank drop.** A proper subset of the simple roots gives an actual standard
Levi of strictly smaller relative semisimple rank. -/
theorem relativeRootRank_leviTorusHom_lt (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) (J : Set (characterLattice T))
    (hJ : J ⊂ simpleRelativeRoots i ν) :
    relativeRootRank (Standard.leviTorusHom i ν J) < relativeRootRank i := by
  obtain ⟨-, -, -, -, -, hLrank, -⟩ := leviScheme_rankPackage hG i hi ν hν J hJ.subset
  obtain ⟨hfin, -, hrank⟩ := relativeSimpleRootBasis k G hG T i hi ν hν
  rw [hLrank, hrank, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  exact Set.ncard_lt_ncard hJ (Set.toFinite _)

open Langlands.Aubert.General.RationalPointFamily in
/-- The strict rank drop for the `Finset` labels of the VI.3.1 target. -/
theorem relativeRootRank_leviTorusHom_rootSet_lt (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν))
    (hI : ∃ a : SimpleRoot i ν, a ∉ I) :
    relativeRootRank (Standard.leviTorusHom i ν (rootSet i ν I)) < relativeRootRank i := by
  apply relativeRootRank_leviTorusHom_lt hG i hi ν hν
  refine ⟨rootSet_subset i ν I, fun h => ?_⟩
  obtain ⟨a, ha⟩ := hI
  exact ha ((val_mem_rootSet i ν I a).mp (h a.property))

/-! ### Standard cocharacters of the Levi -/

/-- A standard cocharacter of `i` for `K ⊆ J` is a standard cocharacter of the Levi
torus `Standard.leviTorusHom i ν J` for `K`. -/
theorem isStandardCocharacter_leviTorusHom (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J K : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) (hKJ : K ⊆ J) {ζ : cocharacterLattice T}
    (hζ : IsStandardCocharacter i ν K ζ) :
    IsStandardCocharacter (Standard.leviTorusHom i ν J) ν K ζ := by
  have hs := simpleRelativeRoots_leviTorusHom hG i hi ν hν J hJ
  refine ⟨?_, hζ.2.1, fun α hα hαK => hζ.2.2 α (hJ ?_) hαK⟩
  · rw [hs]; exact hKJ
  · rw [← hs]; exact hα

/-- The ambient centralizer of a standard cocharacter for `K ⊆ J` lies in `M_J`. -/
theorem centralizer_le_range_leviHom (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J K : Set (characterLattice T)} (hKJ : K ⊆ J)
    {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν K ζ) :
    Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i) ≤
      SubgroupFunctor.range (Standard.leviHom i ν J) := by
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  rw [← ((standardCocharacter k G hG T i hi ν hν K hζ.1).2 ζ hζ).2.1,
    (Standard.isRepresentedBy_leviHom i ν J).2]
  exact standardLevi_mono_of_exists i ν hKJ ⟨ζ, hζ⟩

omit [IsAffineHom G.X.hom] in
theorem groupHom_comp_leviTorusHom_comp [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) (J : Set (characterLattice T)) (ζ : cocharacterLattice T) :
    (CommGroupScheme.groupHom ζ ≫ Standard.leviTorusHom i ν J) ≫ Standard.leviHom i ν J =
      CommGroupScheme.groupHom ζ ≫ i := by
  rw [Category.assoc, Standard.leviTorusHom_comp]

/-! ### Nested dynamic Levis -/

/-- The actual dynamic centralizer of `ζ` in `M_J` is isomorphic to that in `G`. -/
def standardNestedCentralizerIso (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J K : Set (characterLattice T)} (hKJ : K ⊆ J)
    {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν K ζ) :
    Dynamic.Affine.centralizerScheme
        (CommGroupScheme.groupHom ζ ≫ Standard.leviTorusHom i ν J) ≅
      Dynamic.Affine.centralizerScheme (CommGroupScheme.groupHom ζ ≫ i) :=
  nestedCentralizerIso (Standard.leviHom i ν J) _ _ (Standard.isRepresentedBy_leviHom i ν J).1
    (groupHom_comp_leviTorusHom_comp i ν J ζ)
    (centralizer_le_range_leviHom hG i hi ν hν hKJ hζ)

theorem standardNestedCentralizerIso_hom_comp (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J K : Set (characterLattice T)} (hKJ : K ⊆ J)
    {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν K ζ) :
    (standardNestedCentralizerIso hG i hi ν hν hKJ hζ).hom ≫
        Dynamic.Affine.centralizerHom (CommGroupScheme.groupHom ζ ≫ i) =
      Dynamic.Affine.centralizerHom
          (CommGroupScheme.groupHom ζ ≫ Standard.leviTorusHom i ν J) ≫
        Standard.leviHom i ν J :=
  nestedCentralizerIso_hom_comp _ _ _ _ _ _

/-! ### Nested standard Levi schemes -/

/-- For `K ⊆ J ⊆ Δ`, the actual standard Levi of `K` lies in the range of `M_J → G`. -/
theorem standardLevi_le_range_leviHom (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J K : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) (hKJ : K ⊆ J) :
    standardLevi i ν K ≤ SubgroupFunctor.range (Standard.leviHom i ν J) := by
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  rw [(Standard.isRepresentedBy_leviHom i ν J).2]
  exact standardLevi_mono_of_exists i ν hKJ
    (standardCocharacter k G hG T i hi ν hν K (hKJ.trans hJ)).1

/-- For `K ⊆ J ⊆ Δ`, the preimage in `M_J` of the standard Levi of `K` in `G` is the
standard Levi of `K` for the Levi torus of `M_J`. -/
theorem comap_standardLevi_leviHom (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J K : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) (hKJ : K ⊆ J) :
    (standardLevi i ν K).comap (Standard.leviHom i ν J) =
      standardLevi (Standard.leviTorusHom i ν J) ν K :=
  (((leviScheme_rankPackage hG i hi ν hν J hJ).2.2.2.2.2.2 K hKJ).2.1).symm

/-- For `K ⊆ J ⊆ Δ`, the actual standard Levi scheme of `K` for the Levi torus of `M_J`
is isomorphic to the actual standard Levi scheme of `K` for `i`. -/
def standardNestedLeviIso (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J K : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) (hKJ : K ⊆ J) :
    Standard.leviScheme (Standard.leviTorusHom i ν J) ν K ≅ Standard.leviScheme i ν K :=
  nestedIso (Standard.isRepresentedBy_leviHom i ν J).1
    (comap_standardLevi_leviHom hG i hi ν hν hJ hKJ)
    (Standard.isRepresentedBy_leviHom (Standard.leviTorusHom i ν J) ν K)
    (standardLevi_le_range_leviHom hG i hi ν hν hJ hKJ)
    (Standard.isRepresentedBy_leviHom i ν K)

/-- The nested standard Levi isomorphism lies over `G`. -/
theorem standardNestedLeviIso_hom_comp (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J K : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) (hKJ : K ⊆ J) :
    (standardNestedLeviIso hG i hi ν hν hJ hKJ).hom ≫ Standard.leviHom i ν K =
      Standard.leviHom (Standard.leviTorusHom i ν J) ν K ≫ Standard.leviHom i ν J :=
  nestedIso_hom_comp _ _ _ _ _

/-! ### Simple-root labels -/

section Labels

open Langlands.Aubert.General.RationalPointFamily

/-- A simple root of the Levi torus of `M_J` lies in `J`. -/
theorem mem_of_mem_simpleRelativeRoots_leviTorusHom (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) {α : characterLattice T}
    (hα : α ∈ simpleRelativeRoots (Standard.leviTorusHom i ν J) ν) : α ∈ J := by
  rwa [simpleRelativeRoots_leviTorusHom hG i hi ν hν J hJ] at hα

/-- The simple-root labels of the Levi torus of `M_J` are the elements of `J`. -/
def leviSimpleRootEquiv (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) (J : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    SimpleRoot (Standard.leviTorusHom i ν J) ν ≃ J :=
  Equiv.subtypeEquivRight fun _ => by rw [simpleRelativeRoots_leviTorusHom hG i hi ν hν J hJ]

@[simp] theorem leviSimpleRootEquiv_apply_coe (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) (J : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν) (a : SimpleRoot (Standard.leviTorusHom i ν J) ν) :
    ((leviSimpleRootEquiv hG i hi ν hν J hJ a : J) : characterLattice T) = a :=
  rfl

/-- A simple root of the Levi torus of `M_J`, viewed as a simple root of `i`; the
underlying character is unchanged. -/
def ambientSimpleRoot (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    SimpleRoot (Standard.leviTorusHom i ν J) ν ↪ SimpleRoot i ν where
  toFun a := ⟨a.1, hJ (mem_of_mem_simpleRelativeRoots_leviTorusHom hG i hi ν hν hJ a.2)⟩
  inj' a b h := by
    have hv := congrArg Subtype.val h
    exact Subtype.ext hv

@[simp] theorem ambientSimpleRoot_coe (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) (a : SimpleRoot (Standard.leviTorusHom i ν J) ν) :
    ((ambientSimpleRoot hG i hi ν hν hJ a : SimpleRoot i ν) : characterLattice T) = a :=
  rfl

/-- Labels of a standard parabolic of `M_J`, as labels for `i`. -/
def ambientLabels (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (L : Finset (SimpleRoot (Standard.leviTorusHom i ν J) ν)) : Finset (SimpleRoot i ν) :=
  L.map (ambientSimpleRoot hG i hi ν hν hJ)

theorem mem_ambientLabels (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (L : Finset (SimpleRoot (Standard.leviTorusHom i ν J) ν)) (a : SimpleRoot i ν) :
    a ∈ ambientLabels hG i hi ν hν hJ L ↔
      ∃ b ∈ L, ambientSimpleRoot hG i hi ν hν hJ b = a :=
  Finset.mem_map

/-- The ambient labels name the same characters. -/
theorem rootSet_ambientLabels (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (L : Finset (SimpleRoot (Standard.leviTorusHom i ν J) ν)) :
    rootSet i ν (ambientLabels hG i hi ν hν hJ L) =
      rootSet (Standard.leviTorusHom i ν J) ν L := by
  ext α
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
    exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨ambientSimpleRoot hG i hi ν hν hJ b, Finset.mem_map_of_mem _ hb, rfl⟩

/-- The ambient labels lie in `J`. -/
theorem rootSet_ambientLabels_subset (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (L : Finset (SimpleRoot (Standard.leviTorusHom i ν J) ν)) :
    rootSet i ν (ambientLabels hG i hi ν hν hJ L) ⊆ J := by
  rw [rootSet_ambientLabels]
  intro α hα
  exact mem_of_mem_simpleRelativeRoots_leviTorusHom hG i hi ν hν hJ (rootSet_subset _ ν L hα)

/-- Labels for `i`, restricted to the simple roots of the Levi torus of `M_J`. -/
def lowerLabels (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) (I : Finset (SimpleRoot i ν)) :
    Finset (SimpleRoot (Standard.leviTorusHom i ν J) ν) :=
  I.preimage (ambientSimpleRoot hG i hi ν hν hJ)
    (ambientSimpleRoot hG i hi ν hν hJ).injective.injOn

@[simp] theorem mem_lowerLabels (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) (I : Finset (SimpleRoot i ν))
    (a : SimpleRoot (Standard.leviTorusHom i ν J) ν) :
    a ∈ lowerLabels hG i hi ν hν hJ I ↔ ambientSimpleRoot hG i hi ν hν hJ a ∈ I :=
  Finset.mem_preimage

/-- The restricted labels name the characters of `I` lying in `J`. -/
theorem rootSet_lowerLabels (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) (I : Finset (SimpleRoot i ν)) :
    rootSet (Standard.leviTorusHom i ν J) ν (lowerLabels hG i hi ν hν hJ I) =
      rootSet i ν I ∩ J := by
  have hs := simpleRelativeRoots_leviTorusHom hG i hi ν hν J hJ
  ext α
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨ambientSimpleRoot hG i hi ν hν hJ a, Finset.mem_preimage.mp ha, rfl⟩,
      mem_of_mem_simpleRelativeRoots_leviTorusHom hG i hi ν hν hJ a.2⟩
  · rintro ⟨⟨b, hb, rfl⟩, hbJ⟩
    refine ⟨⟨b.1, hs.symm ▸ hbJ⟩, Finset.mem_preimage.mpr ?_, rfl⟩
    have he : ambientSimpleRoot hG i hi ν hν hJ ⟨b.1, hs.symm ▸ hbJ⟩ = b := Subtype.ext rfl
    rw [he]
    exact hb

/-- For `I` with characters in `J`, the restricted labels name exactly the characters
of `I`. -/
theorem rootSet_lowerLabels_of_subset (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) {I : Finset (SimpleRoot i ν)}
    (hIJ : rootSet i ν I ⊆ J) :
    rootSet (Standard.leviTorusHom i ν J) ν (lowerLabels hG i hi ν hν hJ I) =
      rootSet i ν I := by
  rw [rootSet_lowerLabels, Set.inter_eq_left.mpr hIJ]

/-- Restricting and then re-embedding labels with characters in `J` is the identity. -/
theorem ambientLabels_lowerLabels (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) {I : Finset (SimpleRoot i ν)}
    (hIJ : rootSet i ν I ⊆ J) :
    ambientLabels hG i hi ν hν hJ (lowerLabels hG i hi ν hν hJ I) = I := by
  apply rootSet_injective i ν
  rw [rootSet_ambientLabels, rootSet_lowerLabels_of_subset hG i hi ν hν hJ hIJ]

/-- Re-embedding and then restricting labels of `M_J` is the identity. -/
theorem lowerLabels_ambientLabels (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (L : Finset (SimpleRoot (Standard.leviTorusHom i ν J) ν)) :
    lowerLabels hG i hi ν hν hJ (ambientLabels hG i hi ν hν hJ L) = L := by
  apply rootSet_injective (Standard.leviTorusHom i ν J) ν
  rw [rootSet_lowerLabels_of_subset hG i hi ν hν hJ
      (rootSet_ambientLabels_subset hG i hi ν hν hJ L), rootSet_ambientLabels]

/-- For `J = rootSet i ν I'`, the simple-root labels of the Levi torus of `M_J` are the
labels in `I'`. -/
def leviRootLabelEquiv (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) (I' : Finset (SimpleRoot i ν)) :
    SimpleRoot (Standard.leviTorusHom i ν (rootSet i ν I')) ν ≃ {a // a ∈ I'} where
  toFun a := ⟨ambientSimpleRoot hG i hi ν hν (rootSet_subset i ν I') a,
    (val_mem_rootSet i ν I' _).mp
      (mem_of_mem_simpleRelativeRoots_leviTorusHom hG i hi ν hν (rootSet_subset i ν I') a.2)⟩
  invFun b := ⟨b.1.1, (simpleRelativeRoots_leviTorusHom hG i hi ν hν _
      (rootSet_subset i ν I')).symm ▸ (val_mem_rootSet i ν I' b.1).mpr b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem leviRootLabelEquiv_apply_coe (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) (I' : Finset (SimpleRoot i ν))
    (a : SimpleRoot (Standard.leviTorusHom i ν (rootSet i ν I')) ν) :
    (((leviRootLabelEquiv hG i hi ν hν I' a : {a // a ∈ I'}) : SimpleRoot i ν) :
        characterLattice T) = a :=
  rfl

/-- For labels `I ⊆ I'`, the restricted labels of `M_{I'}` name the characters of `I`. -/
theorem rootSet_lowerLabels_rootSet (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {I I' : Finset (SimpleRoot i ν)} (hII' : I ⊆ I') :
    rootSet (Standard.leviTorusHom i ν (rootSet i ν I')) ν
        (lowerLabels hG i hi ν hν (rootSet_subset i ν I') I) = rootSet i ν I :=
  rootSet_lowerLabels_of_subset hG i hi ν hν _ ((rootSet_subset_iff i ν I I').mpr hII')

/-- For labels `I ⊆ I'`, re-embedding the restricted labels of `M_{I'}` gives `I`. -/
theorem ambientLabels_lowerLabels_rootSet (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {I I' : Finset (SimpleRoot i ν)} (hII' : I ⊆ I') :
    ambientLabels hG i hi ν hν (rootSet_subset i ν I')
        (lowerLabels hG i hi ν hν (rootSet_subset i ν I') I) = I :=
  ambientLabels_lowerLabels hG i hi ν hν _ ((rootSet_subset_iff i ν I I').mpr hII')

end Labels

variable [TopologicalSpace k]

/-- A multiplicative homeomorphism between the rational points of the two actual
dynamic Levi schemes; `k` carries an arbitrary topology. -/
def standardNestedCentralizerPointHomeomorph (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J K : Set (characterLattice T)} (hKJ : K ⊆ J)
    {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν K ζ) :
    RationalPoint k (Dynamic.Affine.centralizerScheme
        (CommGroupScheme.groupHom ζ ≫ Standard.leviTorusHom i ν J)).X ≃ₜ*
      RationalPoint k (Dynamic.Affine.centralizerScheme (CommGroupScheme.groupHom ζ ≫ i)).X :=
  nestedCentralizerPointHomeomorph (Standard.leviHom i ν J) _ _
    (Standard.isRepresentedBy_leviHom i ν J).1 (Standard.isClosedSubgroup_leviHom i ν J)
    (groupHom_comp_leviTorusHom_comp i ν J ζ)
    (centralizer_le_range_leviHom hG i hi ν hν hKJ hζ)

theorem standardNestedCentralizerPointHomeomorph_apply (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J K : Set (characterLattice T)} (hKJ : K ⊆ J)
    {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν K ζ)
    (p : RationalPoint k (Dynamic.Affine.centralizerScheme
        (CommGroupScheme.groupHom ζ ≫ Standard.leviTorusHom i ν J)).X) :
    standardNestedCentralizerPointHomeomorph hG i hi ν hν hKJ hζ p =
      p ≫ (standardNestedCentralizerIso hG i hi ν hν hKJ hζ).hom.hom.hom :=
  nestedCentralizerPointHomeomorph_apply _ _ _ _ _ _ _ p

/-- The literal dynamic Levi points of `ζ` in `M_J(k)` and in `G(k)`, identified by the
inclusion `M_J(k) → G(k)`. -/
def standardNestedLeviHomeomorph (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J K : Set (characterLattice T)} (hKJ : K ⊆ J)
    {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν K ζ) :
    (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ Standard.leviTorusHom i ν J)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≃ₜ*
      (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
  nestedLeviHomeomorph (Standard.leviHom i ν J) _ _
    (Standard.isRepresentedBy_leviHom i ν J).1 (Standard.isClosedSubgroup_leviHom i ν J)
    (groupHom_comp_leviTorusHom_comp i ν J ζ)
    (centralizer_le_range_leviHom hG i hi ν hν hKJ hζ)

@[simp] theorem standardNestedLeviHomeomorph_apply_coe (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J K : Set (characterLattice T)} (hKJ : K ⊆ J)
    {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν K ζ)
    (x : (Dynamic.centralizer
        (CommGroupScheme.groupHom ζ ≫ Standard.leviTorusHom i ν J)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    ((standardNestedLeviHomeomorph hG i hi ν hν hKJ hζ x :
        (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).carrier _) :
        RationalPoint k G.X) =
      rationalPoints.map (Standard.leviHom i ν J) (x : RationalPoint k (Standard.leviScheme i ν J).X) :=
  nestedLeviHomeomorph_apply_coe _ _ _ _ _ _ _ x

/-! ### Nested standard Levi points -/

/-- A multiplicative homeomorphism between the rational points of the two actual
standard Levi schemes of `K`; `k` carries an arbitrary topology. -/
def standardNestedLeviPointHomeomorph (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J K : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) (hKJ : K ⊆ J) :
    RationalPoint k (Standard.leviScheme (Standard.leviTorusHom i ν J) ν K).X ≃ₜ*
      RationalPoint k (Standard.leviScheme i ν K).X :=
  nestedPointHomeomorph (Standard.isRepresentedBy_leviHom i ν J).1
    (Standard.isClosedSubgroup_leviHom i ν J) (comap_standardLevi_leviHom hG i hi ν hν hJ hKJ)
    (Standard.isRepresentedBy_leviHom (Standard.leviTorusHom i ν J) ν K)
    (Standard.isClosedSubgroup_leviHom (Standard.leviTorusHom i ν J) ν K)
    (standardLevi_le_range_leviHom hG i hi ν hν hJ hKJ)
    (Standard.isRepresentedBy_leviHom i ν K) (Standard.isClosedSubgroup_leviHom i ν K)

theorem standardNestedLeviPointHomeomorph_apply (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J K : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) (hKJ : K ⊆ J)
    (p : RationalPoint k (Standard.leviScheme (Standard.leviTorusHom i ν J) ν K).X) :
    standardNestedLeviPointHomeomorph hG i hi ν hν hJ hKJ p =
      p ≫ (standardNestedLeviIso hG i hi ν hν hJ hKJ).hom.hom.hom :=
  nestedPointHomeomorph_apply _ _ _ _ _ _ _ _ p

/-- The literal standard Levi points `M_K(k) ⊆ M_J(k)` for the Levi torus of `M_J` and
`M_K(k) ⊆ G(k)` for `i`, with their subspace topologies, are identified by the inclusion
`M_J(k) → G(k)`. -/
def standardNestedLeviPointsHomeomorph (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J K : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) (hKJ : K ⊆ J) :
    standardLeviPoints (Standard.leviTorusHom i ν J) ν K ≃ₜ* standardLeviPoints i ν K :=
  nestedCarrierHomeomorph (h := Standard.leviHom (Standard.leviTorusHom i ν J) ν K)
    (Standard.isRepresentedBy_leviHom i ν J).1 (Standard.isClosedSubgroup_leviHom i ν J)
    (comap_standardLevi_leviHom hG i hi ν hν hJ hKJ)
    (Standard.isRepresentedBy_leviHom (Standard.leviTorusHom i ν J) ν K)
    (Standard.isClosedSubgroup_leviHom (Standard.leviTorusHom i ν J) ν K)
    (standardLevi_le_range_leviHom hG i hi ν hν hJ hKJ)

@[simp] theorem standardNestedLeviPointsHomeomorph_apply_coe (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {J K : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) (hKJ : K ⊆ J)
    (x : standardLeviPoints (Standard.leviTorusHom i ν J) ν K) :
    ((standardNestedLeviPointsHomeomorph hG i hi ν hν hJ hKJ x : standardLeviPoints i ν K) :
        RationalPoint k G.X) =
      rationalPoints.map (Standard.leviHom i ν J)
        (x : RationalPoint k (Standard.leviScheme i ν J).X) :=
  nestedCarrierHomeomorph_apply_coe _ _ _ _ _ _ x

end Standard

end Langlands.GroupScheme.StandardLeviNested
