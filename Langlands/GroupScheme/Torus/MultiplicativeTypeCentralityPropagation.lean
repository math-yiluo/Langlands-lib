import Langlands.GroupScheme.ConnectedFieldOpenProduct
import Langlands.GroupScheme.Torus.MultiplicativeTypeFibrewiseCentralityReduction

/-! # Propagation of centrality from an open unit neighbourhood -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.MultiplicativeTypeCentralityPropagation

open HomScheme MultiplicativeTypeFibrewiseCentralityReduction
  RelativeIdentityComponent

section General

variable {S S' : Scheme.{u}} {H G : GroupScheme S}

/-- Equality of base-changed families gives equality of their relative
evaluations under the actual comparison isomorphisms. -/
theorem evaluate_eq_of_baseChange_eq {M T : Over S} (a : T ⟶ M)
    {f g : RelativeHom H G M}
    (he : (baseChange a.left).map f = (baseChange a.left).map g) :
    evaluate a f = evaluate a g := by
  simp only [evaluate, Descent.pullHom, he]

/-- All-test commutation on a parameter subscheme survives arbitrary base
change of the original source, ambient group and parameter scheme. -/
theorem commute_baseChange (b : S' ⟶ S) (i : H ⟶ G)
    {P : Over S} (j : P ⟶ G.X)
    (hc : ∀ (T : Over S) (a : T ⟶ P) (x : T ⟶ H.X),
      Commute (x ≫ i.hom.hom) (a ≫ j))
    (T : Over S') (a : T ⟶ (Over.pullback b).obj P)
    (x : T ⟶ ((baseChange b).obj H).X) :
    Commute (x ≫ ((baseChange b).map i).hom.hom)
      (a ≫ (Over.pullback b).map j) := by
  let a₀ : (Over.map b).obj T ⟶ P :=
    Over.homMk (a.left ≫ pullback.fst P.hom b) (by
      have ha : a.left ≫ pullback.snd P.hom b = T.hom := Over.w a
      rw [Category.assoc, pullback.condition, ← Category.assoc, ha]
      rfl)
  have hg : baseChangePointsEquiv b G T (a ≫ (Over.pullback b).map j) = a₀ ≫ j := by
    apply Over.OverMorphism.ext
    simp only [baseChangePointsEquiv_left, Over.comp_left, Over.pullback_map_left,
      Category.assoc, pullback.lift_fst, a₀, Over.homMk_left]
  apply (baseChangePointsEquiv b G T).injective
  simp only [map_mul, baseChangePointsEquiv_comp, hg]
  exact hc ((Over.map b).obj T) a₀ (baseChangePointsEquiv b H T x)

/-- Constancy of the conjugation family on a parameter gives all-test
commutation with its image. -/
theorem commute_on_parameter (i : H ⟶ G) {P : Over S} (j : P ⟶ G.X)
    (he : conjugationFamily i j = (baseChange P.hom).map i)
    (T : Over S) (a : T ⟶ P) (x : T ⟶ H.X) :
    Commute (x ≫ i.hom.hom) (a ≫ j) := by
  apply commute_of_conjugationFamily_eq i x (a ≫ j)
  simpa only [evaluate_conjugationFamily, evaluate_baseChange] using
    congrArg (evaluate a) he

end General

section Field

variable {k : Type u} [Field k]
  {H G : GroupScheme (Spec (CommRingCat.of k))}
  [LocallyOfFiniteType G.X.hom] [ConnectedSpace G.X.left]

/-- Commutation with a unit open implies commutation with every point of a
connected field group, by the flat cover from its twofold product. -/
theorem commute_of_unitOpen (i : H ⟶ G)
    {P : Over (Spec (CommRingCat.of k))} (j : P ⟶ G.X) [IsOpenImmersion j.left]
    (he : IdentityComponent.identityPoint G ∈ Set.range j.left)
    (hc : ∀ (T : Over (Spec (CommRingCat.of k))) (a : T ⟶ P) (x : T ⟶ H.X),
      Commute (x ≫ i.hom.hom) (a ≫ j))
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ H.X) (g : T ⟶ G.X) :
    Commute (x ≫ i.hom.hom) g := by
  let p := fieldOpenProduct G j
  have : Flat p.left := ConnectedFieldOpenProduct.flat G j
  have : Surjective p.left := ⟨ConnectedFieldOpenProduct.surjective G j he⟩
  let V : Over (Spec (CommRingCat.of k)) :=
    Over.mk (pullback.fst g.left p.left ≫ T.hom)
  let q : V ⟶ T := Over.homMk (pullback.fst g.left p.left) rfl
  let r : V ⟶ P ⊗ P := Over.homMk (pullback.snd g.left p.left) (by
    rw [← Over.w p, ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w g]
    rfl)
  have hqp : q ≫ g = r ≫ p := by
    apply Over.OverMorphism.ext
    exact pullback.condition
  have hp : p = (fst P P ≫ j) * (snd P P ≫ j) := by
    change (j ⊗ₘ j) ≫ μ[G.X] = _
    rw [Hom.mul_def]
    congr 1
  have hcomm : Commute (q ≫ x ≫ i.hom.hom) (q ≫ g) := by
    rw [hqp, hp, MonObj.comp_mul]
    exact (hc V (r ≫ fst P P) (q ≫ x)).mul_right
      (hc V (r ≫ snd P P) (q ≫ x))
  have : Epi q.left := by
    change Epi (pullback.fst g.left p.left)
    exact Flat.epi_of_flat_of_surjective _
  apply Over.OverMorphism.ext
  apply (cancel_epi q.left).mp
  have hq : q ≫ ((x ≫ i.hom.hom) * g) = q ≫ (g * (x ≫ i.hom.hom)) := by
    simpa only [MonObj.comp_mul, Category.assoc] using hcomm.eq
  exact congrArg (fun a => a.left) hq

/-- A unit open centralizing a homomorphism centralizes the whole connected
field group, including on nonreduced test schemes. -/
theorem isCentral_of_unitOpen (i : H ⟶ G)
    {P : Over (Spec (CommRingCat.of k))} (j : P ⟶ G.X) [IsOpenImmersion j.left]
    (he : IdentityComponent.identityPoint G ∈ Set.range j.left)
    (hc : ∀ (T : Over (Spec (CommRingCat.of k))) (a : T ⟶ P) (x : T ⟶ H.X),
      Commute (x ≫ i.hom.hom) (a ≫ j)) : IsCentral i := by
  intro T x
  apply mem_center.mpr
  intro T' a g
  simpa only [Category.assoc] using commute_of_unitOpen i j he hc T' (a ≫ x) g

end Field

section Relative

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- A centralizing open which contains the unit above a base point centralizes
the entire connected residue fibre. -/
theorem isCentral_residue_of_unitOpen [LocallyOfFiniteType G.X.hom]
    (i : H ⟶ G) {P : Over S} (j : P ⟶ G.X) [IsOpenImmersion j.left]
    (hc : ∀ (T : Over S) (a : T ⟶ P) (x : T ⟶ H.X),
      Commute (x ≫ i.hom.hom) (a ≫ j))
    (t : S)
    (hconn : ConnectedSpace ((baseChange (S.fromSpecResidueField t)).obj G).X.left)
    (he : η[G.X].left t ∈ Set.range j.left) :
    IsCentral ((baseChange (S.fromSpecResidueField t)).map i) := by
  let b := S.fromSpecResidueField t
  let Gt := (baseChange b).obj G
  let j' := (Over.pullback b).map j
  have : LocallyOfFiniteType Gt.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.X.hom b))
  have : ConnectedSpace Gt.X.left := hconn
  have : IsOpenImmersion j'.left :=
    MorphismProperty.of_isPullback (overPullback_isPullback b j).flip inferInstance
  apply isCentral_of_unitOpen (k := S.residueField t) ((baseChange b).map i) j'
  · have hrange := range_of_isPullback (overPullback_isPullback b j)
    have hu : η[Gt.X].left ≫ pullback.fst G.X.hom b = b ≫ η[G.X].left := by
      have h := congrArg (fun x : Over.mk b ⟶ G.X => x.left)
        ((baseChangeBasePointsEquiv b G).map_one)
      rw [baseChangeBasePointsEquiv_left] at h
      exact h
    have hpt : pullback.fst G.X.hom b (IdentityComponent.identityPoint Gt) =
        η[G.X].left t := by
      change (η[Gt.X].left ≫ pullback.fst G.X.hom b)
        (IsLocalRing.closedPoint (S.residueField t)) = _
      rw [hu]
      change η[G.X].left (S.fromSpecResidueField t _) = _
      rw [Scheme.fromSpecResidueField_apply]
    have heunit : IdentityComponent.identityPoint Gt ∈
        pullback.fst G.X.hom b ⁻¹' Set.range j.left :=
      Eq.mpr (congrArg (fun z : G.X.left => z ∈ Set.range j.left) hpt) he
    exact (Set.ext_iff.mp hrange (IdentityComponent.identityPoint Gt)).mpr heunit
  · exact commute_baseChange b i j hc

/-- Central rigidity and connected residue fibres spread a central fibre to
an open neighbourhood of its base point. -/
theorem exists_open_isCentral
    (hRig : MultiplicativeTypeCentralRigidityStatement.{u})
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    [QuasiSeparated G.X.hom] (i : H ⟶ G)
    (hconn : ∀ t : S, ConnectedSpace
      ((baseChange (S.fromSpecResidueField t)).obj G).X.left)
    (s : S) (hs : IsCentral ((baseChange (S.fromSpecResidueField s)).map i)) :
    ∃ U : S.Opens, s ∈ U ∧ IsCentral ((baseChange U.ι).map i) := by
  let t := η[G.X].left s
  have ht : G.X.hom t = s := by
    exact congrArg (fun f : S ⟶ S => f s) (Over.w η[G.X])
  have hct : IsCentral ((baseChange (S.fromSpecResidueField (G.X.hom t))).map i) := by
    exact ht.symm ▸ hs
  let W := centralizingOpenAt hRig hH i t hct
  let P : Over S := Over.mk (W.ι ≫ G.X.hom)
  let j : P ⟶ G.X := Over.homMk W.ι rfl
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion W.ι)
  let U : S.Opens := η[G.X].left ⁻¹ᵁ W
  refine ⟨U, mem_centralizingOpenAt hRig hH i t hct, ?_⟩
  have hW : conjugationFamily i j = (baseChange P.hom).map i := by
    have h := evaluate_eq_of_baseChange_eq j (centralizingOpenAt_eq hRig hH i t hct)
    simpa only [evaluate_conjugationFamily, evaluate_baseChange, Category.comp_id] using h
  have hcW := commute_on_parameter i j hW
  have hcentral (z : S) (hz : z ∈ U) :
      IsCentral ((baseChange (S.fromSpecResidueField z)).map i) := by
    apply isCentral_residue_of_unitOpen i j hcW z (hconn z)
    exact ⟨⟨η[G.X].left z, hz⟩, rfl⟩
  have : LocallyOfFinitePresentation ((baseChange U.ι).obj G).X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.X.hom U.ι))
  have : QuasiCompact ((baseChange U.ι).obj G).X.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd G.X.hom U.ι))
  have : QuasiSeparated ((baseChange U.ι).obj G).X.hom :=
    inferInstanceAs (QuasiSeparated (pullback.snd G.X.hom U.ι))
  apply isCentral_of_fibres_of_centralRigidity hRig (hH.baseChange U.ι)
    ((baseChange U.ι).map i)
  intro z
  apply isCentral_constantFamily_fibre i (Over.mk U.ι) z
  exact hcentral (U.ι z) z.property

/-- A chosen base neighbourhood on which the homomorphism is central. -/
def centralityNeighbourhood
    (hRig : MultiplicativeTypeCentralRigidityStatement.{u})
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    [QuasiSeparated G.X.hom] (i : H ⟶ G)
    (hconn : ∀ t : S, ConnectedSpace
      ((baseChange (S.fromSpecResidueField t)).obj G).X.left)
    (s : S) (hs : IsCentral ((baseChange (S.fromSpecResidueField s)).map i)) :
    S.Opens :=
  (exists_open_isCentral hRig hH i hconn s hs).choose

theorem mem_centralityNeighbourhood
    (hRig : MultiplicativeTypeCentralRigidityStatement.{u})
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    [QuasiSeparated G.X.hom] (i : H ⟶ G)
    (hconn : ∀ t : S, ConnectedSpace
      ((baseChange (S.fromSpecResidueField t)).obj G).X.left)
    (s : S) (hs : IsCentral ((baseChange (S.fromSpecResidueField s)).map i)) :
    s ∈ centralityNeighbourhood hRig hH i hconn s hs :=
  (exists_open_isCentral hRig hH i hconn s hs).choose_spec.1

theorem isCentral_centralityNeighbourhood
    (hRig : MultiplicativeTypeCentralRigidityStatement.{u})
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    [QuasiSeparated G.X.hom] (i : H ⟶ G)
    (hconn : ∀ t : S, ConnectedSpace
      ((baseChange (S.fromSpecResidueField t)).obj G).X.left)
    (s : S) (hs : IsCentral ((baseChange (S.fromSpecResidueField s)).map i)) :
    IsCentral ((baseChange (centralityNeighbourhood hRig hH i hconn s hs).ι).map i) :=
  (exists_open_isCentral hRig hH i hconn s hs).choose_spec.2

end Relative

end Langlands.GroupScheme.MultiplicativeTypeCentralityPropagation
