import Langlands.GroupScheme.Rational.RootSignUnipotentLie
import Langlands.GroupScheme.Rational.SemigroupWeightSupport
import Langlands.GroupScheme.Lie.DimensionInduction
import Langlands.GroupScheme.Lie.SubgroupCellDimension
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Dynamic.ClosedSubgroup
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.UnipotentConnected
import Mathlib.Order.CompactlyGenerated.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Signed dynamic tangent dimensions under closed inclusions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem finrank_signed_weightSums
    {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [DecidableEq I]
    [FiniteDimensional K V]
    (p : I → Submodule K V) (hp : DirectSum.IsInternal p) (w : I → ℤ) :
    Module.finrank K (⨆ i, ⨆ (_ : 0 < w i), p i : Submodule K V) +
      Module.finrank K (⨆ i, ⨆ (_ : w i = 0), p i : Submodule K V) +
      Module.finrank K (⨆ i, ⨆ (_ : w i < 0), p i : Submodule K V) =
        Module.finrank K V := by
  let P : Submodule K V := ⨆ i, ⨆ (_ : 0 < w i), p i
  let Z : Submodule K V := ⨆ i, ⨆ (_ : w i = 0), p i
  let N : Submodule K V := ⨆ i, ⨆ (_ : w i < 0), p i
  have hPZ : Disjoint P Z := hp.submodule_iSupIndep.disjoint_biSup_biSup
    (Set.disjoint_left.mpr fun i hi hj => by
      change 0 < w i at hi
      change w i = 0 at hj
      omega)
  have hPZN : Disjoint (P ⊔ Z) N := by
    have hd : Disjoint ({i | 0 < w i} ∪ {i | w i = 0}) {i | w i < 0} := by
      apply Set.disjoint_left.mpr
      intro i hi hj
      rcases hi with hi | hi
      · change 0 < w i at hi
        change w i < 0 at hj
        omega
      · change w i = 0 at hi
        change w i < 0 at hj
        omega
    simpa only [P, Z, N, iSup_union, Set.mem_ofPred_eq] using
      hp.submodule_iSupIndep.disjoint_biSup_biSup hd
  have htop : P ⊔ Z ⊔ N = ⊤ := by
    apply top_unique
    rw [← hp.submodule_iSup_eq_top]
    refine iSup_le fun i => ?_
    rcases lt_trichotomy 0 (w i) with hi | hi | hi
    · have h : p i ≤ P := le_iSup_of_le i (le_iSup (fun _ : 0 < w i => p i) hi)
      exact (h.trans le_sup_left).trans le_sup_left
    · have h : p i ≤ Z := le_iSup_of_le i (le_iSup (fun _ : w i = 0 => p i) hi.symm)
      exact (h.trans le_sup_right).trans le_sup_left
    · have h : p i ≤ N := le_iSup_of_le i (le_iSup (fun _ : w i < 0 => p i) hi)
      exact h.trans le_sup_right
  have h₁ := Submodule.finrank_sup_add_finrank_inf_eq P Z
  have h₂ := Submodule.finrank_sup_add_finrank_inf_eq (P ⊔ Z) N
  rw [hPZ.eq_bot, finrank_bot, add_zero] at h₁
  rw [hPZN.eq_bot, finrank_bot, add_zero, htop, finrank_top] at h₂
  change Module.finrank K P + Module.finrank K Z + Module.finrank K N = _
  omega

namespace RelativeRoot

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The exact tangent submodule of the dynamic centralizer is the zero pairing span. -/
theorem tangentSubmodule_centralizer_eq_semigroupWeightSpan
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) :
    tangentSubmodule (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)) =
      semigroupWeightSpan (AutomorphicAction.conjugation i) (zeroSemigroup ν) := by
  rw [semigroupWeightSpan_conjugation_zero hS i ν]
  ext X
  exact (dynamicLie k G (CommGroupScheme.groupHom ν ≫ i) X.toMul).1

/-- Positive, zero and negative pairing regions account for the entire actual Lie dimension. -/
theorem finrank_signed_semigroupWeightSpans
    (b : AutomorphicAction S.toGrp G) (hS : IsSplitTorus S.toGrp)
    (ν : cocharacterLattice S) :
    Module.finrank k (semigroupWeightSpan b (positiveSemigroup ν)) +
      Module.finrank k (semigroupWeightSpan b (zeroSemigroup ν)) +
      Module.finrank k (semigroupWeightSpan b (positiveSemigroup (-ν))) = Lie.dimension G := by
  classical
  have hn : (⨆ χ : positiveSemigroup (-ν), actionWeightSpace b χ.val) =
      ⨆ χ : characterLattice S, ⨆ (_ : latticePairing S χ ν < 0),
        actionWeightSpace b χ := by
    rw [iSup_subtype]
    simp only [positiveSemigroup, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, map_neg,
      neg_pos]
  unfold semigroupWeightSpan
  rw [hn, iSup_subtype, iSup_subtype]
  exact finrank_signed_weightSums (actionWeightSpace b)
    (isInternal_actionWeightSpace b hS) (fun χ => latticePairing S χ ν)

/-- The two dynamic identity-limit subgroups and the dynamic centralizer give
an exact three-term formula for the ambient actual Lie dimension. -/
theorem finrank_signed_dynamic_tangentSubmodules
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) :
    Module.finrank k (tangentSubmodule
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i))) +
      Module.finrank k (tangentSubmodule
        (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i))) +
      Module.finrank k (tangentSubmodule
        (Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ i))) = Lie.dimension G := by
  rw [tangentSubmodule_unipotent_eq_semigroupWeightSpan hS i ν,
    tangentSubmodule_centralizer_eq_semigroupWeightSpan hS i ν,
    tangentSubmodule_unipotent_eq_semigroupWeightSpan hS i (-ν)]
  exact finrank_signed_semigroupWeightSpans (AutomorphicAction.conjugation i) hS ν

section Inclusions

variable {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom]
    {F : SubgroupFunctor H} {F' : SubgroupFunctor G}

omit [LocallyOfFiniteType G.X.hom] in
/-- An all-test inclusion along a homomorphism restricts its actual differential
to the intrinsic tangent submodules. -/
def tangentSubmoduleMap (j : H ⟶ G) (h : F ≤ F'.comap j) :
    tangentSubmodule F →ₗ[k] tangentSubmodule F' where
  toFun X := ⟨Lie.targetMapLinear j k X, h _ X.property⟩
  map_add' X Y := Subtype.ext (map_add (Lie.targetMapLinear j k)
    (X : Additive (lieKernel H k)) (Y : Additive (lieKernel H k)))
  map_smul' c X := Subtype.ext (map_smul (Lie.targetMapLinear j k) c
    (X : Additive (lieKernel H k)))

omit [LocallyOfFiniteType G.X.hom] in
/-- Monicity of the actual homomorphism makes its restricted tangent map injective. -/
theorem tangentSubmoduleMap_injective (j : H ⟶ G) [Mono j.hom.hom]
    (h : F ≤ F'.comap j) : Function.Injective (tangentSubmoduleMap j h) := by
  intro X Y hXY
  apply Subtype.ext
  apply Lie.targetMapLinear_injective j k
  exact congrArg (fun Z : tangentSubmodule F' => (Z : Additive (lieKernel G k))) hXY

/-- Tangent dimension is monotone for all-test inclusions along an actual monomorphism. -/
theorem finrank_tangentSubmodule_le_of_le_comap (j : H ⟶ G) [Mono j.hom.hom]
    (h : F ≤ F'.comap j) :
    Module.finrank k (tangentSubmodule F) ≤ Module.finrank k (tangentSubmodule F') :=
  LinearMap.finrank_le_finrank_of_injective (tangentSubmoduleMap_injective j h)

/-- Under an actual inclusion of ambient codimension at most one, both signed
dynamic tangent dimensions have codimension at most one, and one is unchanged. -/
theorem signed_dynamic_dimensions_of_codimension_le_one
    [LocallyOfFiniteType H.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ H) (j : H ⟶ G)
    [Mono j.hom.hom] (ν : cocharacterLattice S)
    (hdim : Lie.dimension G ≤ Lie.dimension H + 1) :
    let pH := Module.finrank k
      (tangentSubmodule (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)))
    let pG := Module.finrank k
      (tangentSubmodule (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i ≫ j)))
    let nH := Module.finrank k
      (tangentSubmodule (Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ i)))
    let nG := Module.finrank k
      (tangentSubmodule (Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ i ≫ j)))
    pG ≤ pH + 1 ∧ nG ≤ nH + 1 ∧ (pG = pH ∨ nG = nH) := by
  have hp := finrank_tangentSubmodule_le_of_le_comap j
    (Dynamic.unipotent_le_comap (CommGroupScheme.groupHom ν ≫ i) j)
  have hz := finrank_tangentSubmodule_le_of_le_comap j
    (Dynamic.centralizer_le_comap (CommGroupScheme.groupHom ν ≫ i) j)
  have hn := finrank_tangentSubmodule_le_of_le_comap j
    (Dynamic.unipotent_le_comap (CommGroupScheme.groupHom (-ν) ≫ i) j)
  rw [Category.assoc] at hp hz hn
  have hH := finrank_signed_dynamic_tangentSubmodules hS i ν
  have hG := finrank_signed_dynamic_tangentSubmodules hS (i ≫ j) ν
  dsimp only
  omega

end Inclusions

end RelativeRoot

namespace SubgroupFunctor.IsRepresentedBy

section Map

variable {S : Scheme.{u}} {H G U V : GroupScheme S}
    {F : SubgroupFunctor H} {F' : SubgroupFunctor G} {i : U ⟶ H} {j : V ⟶ G}

/-- The actual map between represented subgroups induced by an ambient homomorphism. -/
def mapHom (hi : F.IsRepresentedBy i) (hj : F'.IsRepresentedBy j)
    (b : H ⟶ G) (h : F ≤ F'.comap b) : U ⟶ V :=
  hj.factorHom (i ≫ b) (by
    rintro T _ ⟨x, rfl⟩
    change x ≫ (i.hom.hom ≫ b.hom.hom) ∈ F'.carrier T
    rw [← Category.assoc]
    exact h T (hi.pointsEquiv T x).property)

/-- The induced map commutes with the supplied actual inclusions. -/
theorem mapHom_comp (hi : F.IsRepresentedBy i) (hj : F'.IsRepresentedBy j)
    (b : H ⟶ G) (h : F ≤ F'.comap b) :
    mapHom hi hj b h ≫ j = i ≫ b :=
  hj.factorHom_comp _ _

/-- Closed ambient and source inclusions make the induced subgroup map closed. -/
theorem isClosedSubgroup_mapHom (hi : F.IsRepresentedBy i) (hj : F'.IsRepresentedBy j)
    (b : H ⟶ G) (h : F ≤ F'.comap b)
    (hic : IsClosedSubgroup i) (hjc : IsClosedSubgroup j) (hbc : IsClosedSubgroup b) :
    IsClosedSubgroup (mapHom hi hj b h) := by
  apply IsClosedSubgroup.of_comp hjc
  rw [mapHom_comp]
  exact hic.comp hbc

end Map

section Dimension

variable {k : Type u} [Field k] {H G U V : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]
    [IsAffineHom U.X.hom] [IsAffineHom V.X.hom]
    [Smooth U.X.hom] [Smooth V.X.hom] [ConnectedSpace V.X.left]
    {F : SubgroupFunctor H} {F' : SubgroupFunctor G} {i : U ⟶ H} {j : V ⟶ G}

/-- Equality of the intrinsic tangent dimensions gives an isomorphism along
the actual induced closed inclusion into a connected smooth group. -/
theorem isIso_mapHom_of_finrank_eq
    (hi : F.IsRepresentedBy i) (hj : F'.IsRepresentedBy j)
    (b : H ⟶ G) (h : F ≤ F'.comap b)
    (hic : IsClosedSubgroup i) (hjc : IsClosedSubgroup j) (hbc : IsClosedSubgroup b)
    (hdim : Module.finrank k (RelativeRoot.tangentSubmodule F) =
      Module.finrank k (RelativeRoot.tangentSubmodule F')) :
    IsIso (mapHom hi hj b h) := by
  have heq : Lie.dimension U = Lie.dimension V := by
    simpa only [RelativeRoot.finrank_tangentSubmodule_eq_of_isRepresentedBy F i hi,
      RelativeRoot.finrank_tangentSubmodule_eq_of_isRepresentedBy F' j hj,
      Lie.dimension] using hdim
  by_contra hne
  have hlt := Lie.dimension_lt_of_proper_closedSubgroup (mapHom hi hj b h)
    (isClosedSubgroup_mapHom hi hj b h hic hjc hbc) hne
  omega

end Dimension

end SubgroupFunctor.IsRepresentedBy

namespace Dynamic

variable {k : Type u} [Field k]
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- For a smooth closed inclusion of ambient codimension at most one, both
actual signed unipotent inclusions have codimension at most one, and one is an
isomorphism. The ambient groups need not be connected or reductive. -/
theorem signed_unipotent_inclusions_of_codimension_le_one
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ H) (b : H ⟶ G)
    (hbc : IsClosedSubgroup b) (ν : cocharacterLattice S)
    (hdim : Lie.dimension G ≤ Lie.dimension H + 1)
    {Upos Vpos Uneg Vneg : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom Upos.X.hom] [IsAffineHom Vpos.X.hom]
    [IsAffineHom Uneg.X.hom] [IsAffineHom Vneg.X.hom]
    {ipos : Upos ⟶ H} {jpos : Vpos ⟶ G} {ineg : Uneg ⟶ H} {jneg : Vneg ⟶ G}
    (hipos : (unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy ipos)
    (hjpos : (unipotent ((CommGroupScheme.groupHom ν ≫ i) ≫ b)).IsRepresentedBy jpos)
    (hineg : (unipotent (CommGroupScheme.groupHom (-ν) ≫ i)).IsRepresentedBy ineg)
    (hjneg : (unipotent ((CommGroupScheme.groupHom (-ν) ≫ i) ≫ b)).IsRepresentedBy jneg)
    (hicpos : IsClosedSubgroup ipos) (hjcpos : IsClosedSubgroup jpos)
    (hicneg : IsClosedSubgroup ineg) (hjcneg : IsClosedSubgroup jneg) :
    Lie.dimension Vpos ≤ Lie.dimension Upos + 1 ∧
      Lie.dimension Vneg ≤ Lie.dimension Uneg + 1 ∧
      (IsIso (hipos.mapHom hjpos b (unipotent_le_comap _ b)) ∨
        IsIso (hineg.mapHom hjneg b (unipotent_le_comap _ b))) := by
  have : IsClosedImmersion b.hom.hom.left := hbc
  have : Mono b.hom.hom := Over.mono_of_mono_left _
  have : Smooth Upos.X.hom := (dynamicSmooth k H _ Upos ipos).2.2 hipos
  have : Smooth Vpos.X.hom := (dynamicSmooth k G _ Vpos jpos).2.2 hjpos
  have : Smooth Uneg.X.hom := (dynamicSmooth k H _ Uneg ineg).2.2 hineg
  have : Smooth Vneg.X.hom := (dynamicSmooth k G _ Vneg jneg).2.2 hjneg
  have : ConnectedSpace Vpos.X.left :=
    DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent G _ hjpos
  have : ConnectedSpace Vneg.X.left :=
    DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent G _ hjneg
  obtain ⟨hp, hn, he⟩ :=
    RelativeRoot.signed_dynamic_dimensions_of_codimension_le_one hS i b ν hdim
  have hUi := RelativeRoot.finrank_tangentSubmodule_eq_of_isRepresentedBy _ ipos hipos
  have hVj := RelativeRoot.finrank_tangentSubmodule_eq_of_isRepresentedBy _ jpos hjpos
  have hUi' := RelativeRoot.finrank_tangentSubmodule_eq_of_isRepresentedBy _ ineg hineg
  have hVj' := RelativeRoot.finrank_tangentSubmodule_eq_of_isRepresentedBy _ jneg hjneg
  rw [Category.assoc] at hVj hVj'
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hUi, hVj, Lie.dimension] using hp
  · simpa only [hUi', hVj', Lie.dimension] using hn
  · rcases he with he | he
    · left
      apply hipos.isIso_mapHom_of_finrank_eq hjpos b _ hicpos hjcpos hbc
      rw [Category.assoc]
      exact he.symm
    · right
      apply hineg.isIso_mapHom_of_finrank_eq hjneg b _ hicneg hjcneg hbc
      rw [Category.assoc]
      exact he.symm

end Dynamic

end Langlands.GroupScheme
