import Langlands.GroupScheme.Reductive.TitsObstructionSimplyConnected
import Langlands.GroupScheme.Reductive.TitsAlgebraTransport
import Langlands.GroupScheme.Reductive.GaloisPinningIso
import Langlands.GroupScheme.Reductive.GaloisPinningTransport
import Langlands.GroupScheme.Reductive.StarActionIndependenceProof
import Langlands.GroupScheme.MatrixRepresentation.ComponentIntertwiners
import Langlands.GroupScheme.MatrixRepresentation.NormalCharacterSpan

/-! # Transport of the Tits obstruction along pinned isomorphisms and conjugations -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.GaloisPinningData

open MatrixRepresentation Langlands.Brauer

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G G' : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [IsAffineHom G'.X.hom]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType G'.X.hom]
  {d : GaloisPinningData k K G} {d' : GaloisPinningData k K G'}

local instance titsObstructionTransportAffine {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj H).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd H.X.hom (algebraBaseMap k K))
  infer_instance

namespace Iso

variable (f : d.Iso d')

theorem weightMap_mem_starFixedWeights_iff (lam : characterLattice d.toSplitPinning.torus) :
    f.weightMap lam ∈ d'.starFixedWeights ↔ lam ∈ d.starFixedWeights := by
  rw [d'.mem_starFixedWeights, d.mem_starFixedWeights]
  exact f.isStarFixedWeight_weightMap_iff lam

/-- The isomorphism of star-fixed weight groups induced by a pinned isomorphism. -/
def starFixedWeightsEquiv : d.starFixedWeights ≃+ d'.starFixedWeights where
  toFun x := ⟨f.weightMap x.1, (f.weightMap_mem_starFixedWeights_iff x.1).mpr x.2⟩
  invFun y := ⟨f.weightMap.symm y.1, by
    rw [← f.weightMap_mem_starFixedWeights_iff, LinearEquiv.apply_symm_apply]
    exact y.2⟩
  left_inv x := Subtype.ext (f.weightMap.symm_apply_apply x.1)
  right_inv y := Subtype.ext (f.weightMap.apply_symm_apply y.1)
  map_add' x y := Subtype.ext (map_add f.weightMap x.1 y.1)

theorem coe_starFixedWeightsEquiv (x : d.starFixedWeights) :
    (f.starFixedWeightsEquiv x : characterLattice d'.toSplitPinning.torus) = f.weightMap x.1 :=
  rfl

variable [IsGalois k K]

/-- The Tits algebra of a representation of `G'_K` of star-fixed highest weight `f.weightMap λ`
is Brauer equivalent to that of its restriction to `G_K`, which has highest weight `λ`. -/
theorem titsCSAOf_restrict_isBrauerEquivalent {n : ℕ}
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G') (Fin n)}
    {lam : characterLattice d.toSplitPinning.torus}
    (hρ' : d'.toSplitPinning.IsHighestWeight ρ (f.weightMap lam))
    (hρ : d.toSplitPinning.IsHighestWeight (ρ.restrict f.baseChangeGroupIso.hom) lam)
    (hfix : d.IsStarFixedWeight lam) (hfix' : d'.IsStarFixedWeight (f.weightMap lam)) :
    IsBrauerEquivalent (d.titsCSAOf hρ hfix) (d'.titsCSAOf hρ' hfix') := by
  have := d'.nonempty_of_isHighestWeight hρ'
  have h : titsAlgebra (ρ.restrict f.baseChangeGroupIso.hom) = titsAlgebra ρ :=
    titsAlgebra_restrict_iso ρ hρ'.1
      (SplitPinning.IsHighestWeight.intertwiner_eq_scalar d'.toSplitPinning hρ')
      (fun σ => (d'.exists_intertwiner_galoisTwist hρ' hfix' σ).choose)
      (fun σ => (d'.exists_intertwiner_galoisTwist hρ' hfix' σ).choose_spec.2)
      (fun σ => (d'.exists_intertwiner_galoisTwist hρ' hfix' σ).choose_spec.1) f.groupIso
  exact ⟨1, 1, one_ne_zero, one_ne_zero, ⟨(Subalgebra.equivOfEq _ _ h).mapMatrix⟩⟩

/-- On dominant star-fixed weights, the dominant Tits classes correspond. -/
theorem dominantTitsClass_weightMap (lam : characterLattice d.toSplitPinning.torus)
    (hdom : d.toSplitPinning.IsDominantWeight lam) (hfix : d.IsStarFixedWeight lam)
    (hdom' : d'.toSplitPinning.IsDominantWeight (f.weightMap lam))
    (hfix' : d'.IsStarFixedWeight (f.weightMap lam)) :
    d'.dominantTitsClass (f.weightMap lam) hdom' hfix' = d.dominantTitsClass lam hdom hfix := by
  obtain ⟨n, ρ, hρ'⟩ :=
    (splitHighestWeightClassification K _ d'.toSplitPinning).1 (f.weightMap lam) hdom'
  have hρ : d.toSplitPinning.IsHighestWeight (ρ.restrict f.baseChangeGroupIso.hom) lam :=
    (f.isHighestWeight_restrict_iff ρ lam).mpr hρ'
  rw [d'.dominantTitsClass_eq hdom' hfix' hρ', d.dominantTitsClass_eq hdom hfix hρ]
  exact (Quotient.sound (f.titsCSAOf_restrict_isBrauerEquivalent hρ' hρ hfix hfix')).symm

/-- **Transport of the Tits obstruction.** For simply connected `G` and `G'` and a pinned
isomorphism `f : d.Iso d'`, the obstruction of `d'` at the transported weight equals the
obstruction of `d`. -/
theorem titsObstruction_starFixedWeightsEquiv (hG : IsSimplyConnected G)
    (hG' : IsSimplyConnected G') (lam : d.starFixedWeights) :
    d'.titsObstruction hG' (f.starFixedWeightsEquiv lam) = d.titsObstruction hG lam := by
  have hspan := d.corootSpan_eq_top_of_simplyConnected hG
  have hfix : d.IsStarFixedWeight lam.1 := d.isStarFixedWeight_of_mem_starFixedWeights lam.2
  set a := d.dominantPart hspan lam.1
  have ha : d.toSplitPinning.IsDominantWeight a := d.isDominantWeight_dominantPart hspan lam.1
  have hb : d.toSplitPinning.IsDominantWeight (a - lam.1) :=
    d.isDominantWeight_dominantPart_sub hspan lam.1
  have hfa : d.IsStarFixedWeight a := d.isStarFixedWeight_dominantPart hspan hfix
  have hfb : d.IsStarFixedWeight (a - lam.1) := d.isStarFixedWeight_sub hfa hfix
  have ha' := (f.isDominantWeight_weightMap_iff a).mpr ha
  have hb' := (f.isDominantWeight_weightMap_iff (a - lam.1)).mpr hb
  have hfa' := (f.isStarFixedWeight_weightMap_iff a).mpr hfa
  have hfb' := (f.isStarFixedWeight_weightMap_iff (a - lam.1)).mpr hfb
  have : AddMonoidHomClass (characterLattice d.toSplitPinning.torus ≃ₗ[ℤ]
      characterLattice d'.toSplitPinning.torus) (characterLattice d.toSplitPinning.torus)
      (characterLattice d'.toSplitPinning.torus) :=
    SemilinearMapClass.instAddMonoidHomClass _
  rw [d.titsObstruction_eq_sub hG lam ha hb hfa hfb (sub_sub_cancel a lam.1).symm,
    d'.titsObstruction_eq_sub hG' (f.starFixedWeightsEquiv lam) ha' hb' hfa' hfb'
      (by rw [coe_starFixedWeightsEquiv, ← map_sub, sub_sub_cancel]),
    f.dominantTitsClass_weightMap a ha hfa ha' hfa',
    f.dominantTitsClass_weightMap (a - lam.1) hb hfb hb' hfb']

/-- The transport identity in composite form: the obstruction of `d` is the obstruction of
`d'` composed with the induced isomorphism of star-fixed weights. -/
theorem titsObstruction_comp_starFixedWeightsEquiv (hG : IsSimplyConnected G)
    (hG' : IsSimplyConnected G') :
    (d'.titsObstruction hG').comp f.starFixedWeightsEquiv.toAddMonoidHom =
      d.titsObstruction hG :=
  AddMonoidHom.ext fun lam => f.titsObstruction_starFixedWeightsEquiv hG hG' lam

end Iso

end Langlands.GroupScheme.GaloisPinningData

namespace Langlands.GroupScheme.MatrixRepresentation

open scoped CategoryTheory.MonObj

variable {F : Type u} [Field F] {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom H.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

/-- The matrix of a rational point `g` intertwines a representation with its restriction along
the inner automorphism by `g`: `ρ(g) ρ(x) = ρ(g x g⁻¹) ρ(g)`. -/
theorem intertwines_restrict_innerIso (ρ : MatrixRepresentation H n)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ H.X) :
    ρ.Intertwines (ρ.restrict (H.innerIso g).hom) (ρ.rationalMatrix g : Matrix n n F) := by
  rw [intertwines_iff_universal_pointMatrix, pointMatrix_restrict, comp_innerIso_hom, map_mul,
    map_mul, map_inv, pointMatrix_constantPoint]
  have hA : (ρ.rationalMatrix g : Matrix n n F).map (scalarMap H.X) =
      ((Matrix.GeneralLinearGroup.map (scalarMap H.X) (ρ.rationalMatrix g) :
        GL n Γ(H.X.left, ⊤)) : Matrix n n Γ(H.X.left, ⊤)) := rfl
  rw [hA, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.GaloisPinningData

open MatrixRepresentation Langlands.Brauer

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance titsObstructionConjAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- A pinned conjugation between two Galois pinning data of the same group: a point `g` of
`G_K` over `K` whose inner automorphism carries the split torus of `d` onto that of `d'`
through a torus isomorphism `φ` over `K`, together with a base-preserving equivalence of the
root data whose weight map is the character map of `φ`. -/
structure Conj (d d' : GaloisPinningData k K G) where
  /-- The conjugating point of `G_K`. -/
  point : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X
  /-- The induced isomorphism of the split tori over `K`. -/
  torusIso : d.toSplitPinning.torus ≅ d'.toSplitPinning.torus
  square : d.toSplitPinning.inclusion ≫
      (((GroupScheme.baseChange (algebraBaseMap k K)).obj G).innerIso point).hom =
    CommGroupScheme.groupHom torusIso.hom ≫ d'.toSplitPinning.inclusion
  /-- The equivalence of root data. -/
  rootDatumEquiv : RootPairing.Equiv d.toSplitPinning.rootDatum d'.toSplitPinning.rootDatum
  weightMap_eq : ∀ χ, rootDatumEquiv.weightMap χ = characterLattice.congr torusIso χ
  base_iff : ∀ a, a ∈ d.toSplitPinning.base.support ↔
    rootDatumEquiv.indexEquiv a ∈ d'.toSplitPinning.base.support

namespace Conj

/-- Any two Galois pinning data of the same group are related by a pinned conjugation
(the Library's `starActionIndependence`). -/
theorem nonempty [LocallyOfFiniteType G.X.hom] (d d' : GaloisPinningData k K G) :
    Nonempty (d.Conj d') := by
  obtain ⟨g, φ, e, hg, he, hb, -⟩ := StarActionIndependence.starActionIndependence k K G d d'
  exact ⟨⟨g, φ, hg, e, fun χ => congrFun he χ, hb⟩⟩

variable {d d' : GaloisPinningData k K G} (f : d.Conj d')

/-- The weight map of a pinned conjugation. -/
def weightMap : characterLattice d.toSplitPinning.torus ≃ₗ[ℤ]
    characterLattice d'.toSplitPinning.torus :=
  f.rootDatumEquiv.weightEquiv

theorem weightMap_apply (χ : characterLattice d.toSplitPinning.torus) :
    f.weightMap χ = f.rootDatumEquiv.weightMap χ :=
  rfl

theorem isDominantWeight_weightMap_iff (χ : characterLattice d.toSplitPinning.torus) :
    d'.toSplitPinning.IsDominantWeight (f.weightMap χ) ↔ d.toSplitPinning.IsDominantWeight χ :=
  SplitPinning.isDominantWeight_weightMap_iff f.rootDatumEquiv f.base_iff χ

/-- A representation of `G_K` has highest weight `f.weightMap λ` for `d'` exactly when its
restriction along the inner automorphism by `f.point` has highest weight `λ` for `d`. -/
theorem isHighestWeight_restrict_iff {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (lam : characterLattice d.toSplitPinning.torus) :
    d.toSplitPinning.IsHighestWeight
        (ρ.restrict (((GroupScheme.baseChange (algebraBaseMap k K)).obj G).innerIso
          f.point).hom) lam ↔
      d'.toSplitPinning.IsHighestWeight ρ (f.weightMap lam) :=
  SplitPinning.isHighestWeight_restrict_iso_iff _ f.torusIso f.square f.rootDatumEquiv
    f.weightMap_eq f.base_iff ρ lam

variable [LocallyOfFiniteType G.X.hom]

/-- **Star compatibility** (the Library's `StarActionIndependence.starAction_intertwine`). -/
theorem rootDatumEquiv_comp_starAction (σ : K ≃ₐ[k] K) :
    f.rootDatumEquiv.comp (d.starAction σ).val = (d'.starAction σ).val.comp f.rootDatumEquiv :=
  StarActionIndependence.starAction_intertwine d d' f.rootDatumEquiv f.square
    (fun χ => f.weightMap_eq χ) f.base_iff σ

theorem starAction_weightMap (σ : K ≃ₐ[k] K) (χ : characterLattice d.toSplitPinning.torus) :
    (d'.starAction σ).val.weightEquiv (f.weightMap χ) =
      f.weightMap ((d.starAction σ).val.weightEquiv χ) := by
  have h := congrArg (fun g : RootPairing.Equiv d.toSplitPinning.rootDatum
    d'.toSplitPinning.rootDatum => g.weightMap χ) (f.rootDatumEquiv_comp_starAction σ)
  exact h.symm

theorem isStarFixedWeight_weightMap_iff (χ : characterLattice d.toSplitPinning.torus) :
    d'.IsStarFixedWeight (f.weightMap χ) ↔ d.IsStarFixedWeight χ := by
  refine forall_congr' fun σ => ?_
  rw [f.starAction_weightMap]
  exact f.weightMap.injective.eq_iff

theorem weightMap_mem_starFixedWeights_iff (lam : characterLattice d.toSplitPinning.torus) :
    f.weightMap lam ∈ d'.starFixedWeights ↔ lam ∈ d.starFixedWeights := by
  rw [d'.mem_starFixedWeights, d.mem_starFixedWeights]
  exact f.isStarFixedWeight_weightMap_iff lam

/-- The isomorphism of star-fixed weight groups induced by a pinned conjugation. -/
def starFixedWeightsEquiv : d.starFixedWeights ≃+ d'.starFixedWeights where
  toFun x := ⟨f.weightMap x.1, (f.weightMap_mem_starFixedWeights_iff x.1).mpr x.2⟩
  invFun y := ⟨f.weightMap.symm y.1, by
    rw [← f.weightMap_mem_starFixedWeights_iff, LinearEquiv.apply_symm_apply]
    exact y.2⟩
  left_inv x := Subtype.ext (f.weightMap.symm_apply_apply x.1)
  right_inv y := Subtype.ext (f.weightMap.apply_symm_apply y.1)
  map_add' x y := Subtype.ext (map_add f.weightMap x.1 y.1)

theorem coe_starFixedWeightsEquiv (x : d.starFixedWeights) :
    (f.starFixedWeightsEquiv x : characterLattice d'.toSplitPinning.torus) = f.weightMap x.1 :=
  rfl

variable [IsGalois k K]

/-- The Tits algebras of a representation `ρ` of `G_K` and of its restriction along the inner
automorphism by `f.point` are Brauer equivalent. -/
theorem titsCSAOf_restrict_isBrauerEquivalent {n : ℕ}
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) (Fin n)}
    {lam : characterLattice d.toSplitPinning.torus}
    (hρ' : d'.toSplitPinning.IsHighestWeight ρ (f.weightMap lam))
    (hρ : d.toSplitPinning.IsHighestWeight
      (ρ.restrict (((GroupScheme.baseChange (algebraBaseMap k K)).obj G).innerIso
        f.point).hom) lam)
    (hfix : d.IsStarFixedWeight lam) (hfix' : d'.IsStarFixedWeight (f.weightMap lam)) :
    IsBrauerEquivalent (d.titsCSAOf hρ hfix) (d'.titsCSAOf hρ' hfix') := by
  let C := ρ.rationalMatrix f.point
  have hCD : (C : Matrix (Fin n) (Fin n) K) * (C⁻¹ : GL (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hDC : ((C⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * C = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  exact ⟨1, 1, one_ne_zero, one_ne_zero, ⟨(titsAlgebraEquivOfIntertwines (k := k)
    (intertwines_restrict_innerIso ρ f.point) _ hCD hDC).symm.mapMatrix⟩⟩

/-- On dominant star-fixed weights, the dominant Tits classes correspond under a pinned
conjugation. -/
theorem dominantTitsClass_weightMap (lam : characterLattice d.toSplitPinning.torus)
    (hdom : d.toSplitPinning.IsDominantWeight lam) (hfix : d.IsStarFixedWeight lam)
    (hdom' : d'.toSplitPinning.IsDominantWeight (f.weightMap lam))
    (hfix' : d'.IsStarFixedWeight (f.weightMap lam)) :
    d'.dominantTitsClass (f.weightMap lam) hdom' hfix' = d.dominantTitsClass lam hdom hfix := by
  obtain ⟨n, ρ, hρ'⟩ :=
    (splitHighestWeightClassification K _ d'.toSplitPinning).1 (f.weightMap lam) hdom'
  have hρ := (f.isHighestWeight_restrict_iff ρ lam).mpr hρ'
  rw [d'.dominantTitsClass_eq hdom' hfix' hρ', d.dominantTitsClass_eq hdom hfix hρ]
  exact (Quotient.sound (f.titsCSAOf_restrict_isBrauerEquivalent hρ' hρ hfix hfix')).symm

/-- **Independence of the Galois pinning data.** For a simply connected group and a pinned
conjugation `f` between two Galois pinning data `d`, `d'` of it, the obstruction of `d'` at the
transported weight equals the obstruction of `d`. -/
theorem titsObstruction_starFixedWeightsEquiv (hG : IsSimplyConnected G)
    (lam : d.starFixedWeights) :
    d'.titsObstruction hG (f.starFixedWeightsEquiv lam) = d.titsObstruction hG lam := by
  have hspan := d.corootSpan_eq_top_of_simplyConnected hG
  have hfix : d.IsStarFixedWeight lam.1 := d.isStarFixedWeight_of_mem_starFixedWeights lam.2
  set a := d.dominantPart hspan lam.1
  have ha : d.toSplitPinning.IsDominantWeight a := d.isDominantWeight_dominantPart hspan lam.1
  have hb : d.toSplitPinning.IsDominantWeight (a - lam.1) :=
    d.isDominantWeight_dominantPart_sub hspan lam.1
  have hfa : d.IsStarFixedWeight a := d.isStarFixedWeight_dominantPart hspan hfix
  have hfb : d.IsStarFixedWeight (a - lam.1) := d.isStarFixedWeight_sub hfa hfix
  have ha' := (f.isDominantWeight_weightMap_iff a).mpr ha
  have hb' := (f.isDominantWeight_weightMap_iff (a - lam.1)).mpr hb
  have hfa' := (f.isStarFixedWeight_weightMap_iff a).mpr hfa
  have hfb' := (f.isStarFixedWeight_weightMap_iff (a - lam.1)).mpr hfb
  have : AddMonoidHomClass (characterLattice d.toSplitPinning.torus ≃ₗ[ℤ]
      characterLattice d'.toSplitPinning.torus) (characterLattice d.toSplitPinning.torus)
      (characterLattice d'.toSplitPinning.torus) :=
    SemilinearMapClass.instAddMonoidHomClass _
  rw [d.titsObstruction_eq_sub hG lam ha hb hfa hfb (sub_sub_cancel a lam.1).symm,
    d'.titsObstruction_eq_sub hG (f.starFixedWeightsEquiv lam) ha' hb' hfa' hfb'
      (by rw [coe_starFixedWeightsEquiv, ← map_sub, sub_sub_cancel]),
    f.dominantTitsClass_weightMap a ha hfa ha' hfa',
    f.dominantTitsClass_weightMap (a - lam.1) hb hfb hb' hfb']

theorem titsObstruction_comp_starFixedWeightsEquiv (hG : IsSimplyConnected G) :
    (d'.titsObstruction hG).comp f.starFixedWeightsEquiv.toAddMonoidHom =
      d.titsObstruction hG :=
  AddMonoidHom.ext fun lam => f.titsObstruction_starFixedWeightsEquiv hG lam

end Conj

/-- **Independence of the Galois pinning data**, existence form: for any two Galois pinning
data of a simply connected group there is an isomorphism of their star-fixed weight groups,
induced by a base-preserving equivalence of root data coming from a conjugation of the tori,
that identifies the two obstructions. -/
theorem exists_starFixedWeightsEquiv_titsObstruction [LocallyOfFiniteType G.X.hom]
    [IsGalois k K] (hG : IsSimplyConnected G) (d d' : GaloisPinningData k K G) :
    ∃ f : d.Conj d', (d'.titsObstruction hG).comp f.starFixedWeightsEquiv.toAddMonoidHom =
      d.titsObstruction hG :=
  let f := (Conj.nonempty d d').some
  ⟨f, f.titsObstruction_comp_starFixedWeightsEquiv hG⟩

section IsoInvariance

variable {G' : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G'.X.hom]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType G'.X.hom] [IsGalois k K]

/-- **Isomorphism invariance of the obstruction.** For a `k`-isomorphism `e : G ≅ G'` of simply
connected groups, Galois pinning data `d` of `G` and `d'` of `G'`, and a pinned conjugation `f`
from the transport of `d` along `e` to `d'`, the obstruction of `d'` at the image of `λ` under
the composite identification of star-fixed weights equals the obstruction of `d` at `λ`. -/
theorem titsObstruction_transport_conj (hG : IsSimplyConnected G)
    (hG' : IsSimplyConnected G') (e : G ≅ G') {d : GaloisPinningData k K G}
    {d' : GaloisPinningData k K G'} (f : (d.transport e).Conj d') (lam : d.starFixedWeights) :
    d'.titsObstruction hG'
        (f.starFixedWeightsEquiv ((d.transportIso e).starFixedWeightsEquiv lam)) =
      d.titsObstruction hG lam := by
  rw [f.titsObstruction_starFixedWeightsEquiv hG',
    (d.transportIso e).titsObstruction_starFixedWeightsEquiv hG hG']

/-- **Isomorphism invariance**, existence form: for a `k`-isomorphism of simply connected groups
`G ≅ G'` and any Galois pinning data `d` of `G` and `d'` of `G'`, some isomorphism of the
star-fixed weight groups, obtained by composing the transport along `e` with a pinned
conjugation, identifies the two obstructions. -/
theorem exists_starFixedWeightsEquiv_titsObstruction_of_iso (hG : IsSimplyConnected G)
    (hG' : IsSimplyConnected G') (e : G ≅ G') (d : GaloisPinningData k K G)
    (d' : GaloisPinningData k K G') :
    ∃ φ : d.starFixedWeights ≃+ d'.starFixedWeights,
      (d'.titsObstruction hG').comp φ.toAddMonoidHom = d.titsObstruction hG := by
  let f := (Conj.nonempty (d.transport e) d').some
  exact ⟨(d.transportIso e).starFixedWeightsEquiv.trans f.starFixedWeightsEquiv,
    AddMonoidHom.ext fun lam => titsObstruction_transport_conj hG hG' e f lam⟩

end IsoInvariance

end Langlands.GroupScheme.GaloisPinningData
