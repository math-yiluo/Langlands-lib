import Langlands.GroupScheme.Rational.TypeD5ClosedSubgroupRank
import Langlands.GroupScheme.Rational.TypeE6CubicSplitLargeSubgroup
import Langlands.GroupScheme.Lie.SmoothFibreRanks
import Langlands.GroupScheme.Reductive.AbsoluteCartanClassificationStatement
import Langlands.GroupScheme.Reductive.PinningNumberingBaseChange
import Langlands.GroupScheme.Reductive.SplitPinningExistenceProof
import Langlands.GroupScheme.Reductive.TitsComponentFactorProof
import Langlands.GroupScheme.Reductive.TitsIndexExistenceProof
import Langlands.GroupScheme.Torus.CentralRigidityReduction
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.LinearAlgebra.CartanD5F4RootCounts
import Langlands.LinearAlgebra.SmallTypeAComponentRootBound

/-! # An anisotropic factor outside type A in the cubic splitting argument -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped BigOperators TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.LinearAlgebra.SimplyConnectedCartanComponents

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000
set_option synthInstance.maxHeartbeats 100000

private local instance affineBaseChange {S T : Scheme.{u}} (b : T ⟶ S) (G : GroupScheme S)
    [IsAffineHom G.X.hom] : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd _ _ ‹IsAffineHom G.X.hom›

private local instance finiteTypeBaseChange {S T : Scheme.{u}} (b : T ⟶ S) (G : GroupScheme S)
    [LocallyOfFiniteType G.X.hom] : LocallyOfFiniteType ((GroupScheme.baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd _ _ ‹LocallyOfFiniteType G.X.hom›

private theorem lieDimension_baseChange {k E : Type u} [Field k] [Field E] [Algebra k E]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] [Smooth G.X.hom] :
    Lie.dimension ((GroupScheme.baseChange (algebraBaseMap k E)).obj G) = Lie.dimension G := by
  let : Module.Free (CommRingCat.of k) (Additive (lieKernel G (CommRingCat.of k))) :=
    inferInstanceAs (Module.Free k (Additive (lieKernel G k)))
  change Module.finrank E (Additive (lieKernel ((GroupScheme.baseChange (algebraBaseMap k E)).obj G) E)) =
    Module.finrank k (Additive (lieKernel G k))
  rw [(Lie.kernelBaseChangeLinearEquiv (CommRingCat.of k) E G E).finrank_eq,
    ← (Lie.smoothKernelScalarExtension G E).finrank_eq, Module.finrank_baseChange]

private theorem nonempty_rootIndexEquiv_of_derived
    {k : Type u} [Field k] {H D : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom] [IsAffineHom D.X.hom]
    [LocallyOfFiniteType D.X.hom] (p : SplitPinning H) (q : SplitPinning D)
    (i : D ⟶ H) (hi : IsDerivedSubgroup i) : Nonempty (q.rootIndex ≃ p.rootIndex) := by
  let ν : cocharacterLattice p.torus := 0
  let χ := CommGroupScheme.groupHom ν ≫ p.inclusion
  have hχ : χ = 0 := by
    change CommGroupScheme.groupHom (0 : cocharacterLattice p.torus) ≫ p.inclusion = 0
    rw [show CommGroupScheme.groupHom (0 : cocharacterLattice p.torus) = 0 from rfl]
    apply Grp.hom_ext
    simp only [Grp.comp_hom_hom, CentralRigidity.zero_hom_hom, MonObj.one_comp]
  have hrep : (Dynamic.centralizer χ).IsRepresentedBy (𝟙 H) := by
    rw [← torusCentralizer_gm_eq_dynamicCentralizer, hχ]
    refine ⟨inferInstance, SubgroupFunctor.ext fun T => Subgroup.ext fun x => ?_⟩
    rw [mem_torusCentralizer, SubgroupFunctor.mem_range]
    constructor
    · intro _ V a t
      rw [CentralRigidity.zero_hom_hom, MonObj.comp_one]
      exact Commute.one_right _
    · intro _
      exact ⟨x, by simp⟩
  obtain ⟨⟨Q⟩, _⟩ := p.standardLeviDerivedPinning ν (by intro a; simp [ν]) (𝟙 H) hrep i hi
  obtain ⟨r⟩ := nonempty_rootDatumEquiv_of_iso q.isConnectedReductive Q.pinning.isConnectedReductive
    q.isSplitTorus Q.pinning.isSplitTorus q.isMaximalTorus Q.pinning.isMaximalTorus (Iso.refl D)
    q.isRootDatum Q.pinning.isRootDatum
  let s : {a : p.rootIndex // p.rootDatum.root' a ν = 0} ≃ p.rootIndex :=
    Equiv.ofBijective Subtype.val ⟨Subtype.val_injective, fun a => ⟨⟨a, by simp [ν]⟩, rfl⟩⟩
  exact ⟨r.indexEquiv.trans (Q.face.indexEquiv.trans s)⟩

section Dimension

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G H A D : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  [IsAffineHom A.X.hom] [LocallyOfFiniteType A.X.hom]
  [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]

/-- A reductive subgroup of an absolute rank-six simply connected group
has dimension at most twenty-eight if its derived group embeds in split
simply connected D5 and all of its Cartan components have type A. -/
theorem SplitPinning.lieDimension_le_of_typeA_components_in_typeD5
    (g : SplitPinning G) (p : SplitPinning H) (s : SplitPinning A) (q : SplitPinning D)
    (hsc : IsSimplyConnected G) (hg : Nat.card g.base.support = 6)
    (hscD : IsSimplyConnected D) (e : q.base.support ≃ Fin 5)
    (hD : ∀ a b, q.rootDatum.pairing a.val b.val = CartanMatrix.D 5 (e a) (e b))
    (j : H ⟶ G) (hj : IsClosedSubgroup j) (i : A ⟶ H) (hi : IsDerivedSubgroup i)
    (f : A ⟶ D) (hf : IsClosedSubgroup f)
    (hA : ∀ c : Component s.base, ∃ (n : ℕ) (w : {a : s.base.support // component s.base a = c} ≃ Fin n),
      ∀ a b, s.rootDatum.pairing (w.symm a).val.val (w.symm b).val.val = CartanMatrix.A n a b) :
    Lie.dimension H ≤ 28 := by
  let : IsAffineHom g.torus.toGrp.X.hom := g.isSplitTorus.isAffineHom
  let : IsAffineHom p.torus.toGrp.X.hom := p.isSplitTorus.isAffineHom
  let : IsAffineHom s.torus.toGrp.X.hom := s.isSplitTorus.isAffineHom
  let : IsAffineHom q.torus.toGrp.X.hom := q.isSplitTorus.isAffineHom
  have hrG : Lie.dimension g.torus.toGrp = 6 := (g.torusDimension_eq_card_base_of_isSimplyConnected hsc).trans hg
  have hrH : Lie.dimension p.torus.toGrp ≤ 6 := hrG ▸ (p.torusDimension_le_of_closedSubgroup g j hj).1
  have hrD : Lie.dimension q.torus.toGrp = 5 := by
    rw [q.torusDimension_eq_card_base_of_isSimplyConnected hscD, Nat.card_congr e, Nat.card_fin]
  have hrA : Nat.card s.base.support ≤ 5 :=
    s.card_base_le_torusDimension.trans (hrD ▸ (s.torusDimension_le_of_closedSubgroup q f hf).1)
  let : s.rootDatum.IsReduced := s.isReduced
  have hcard : Nat.card s.rootIndex ≤ 22 := by
    apply Langlands.LinearAlgebra.card_root_le_22_of_small_typeA_components _ _ hrA
    intro c
    obtain ⟨n, w, hw⟩ := hA c
    have hr : Nat.card {a : s.base.support // component s.base a = c} = n :=
      (Nat.card_congr w).trans (Nat.card_fin n)
    have hle : n ≤ Nat.card s.base.support := by
      rw [← hr]
      exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    refine ⟨n, ?_, w, hw⟩
    by_contra! hn
    have hn5 : n = 5 := by omega
    subst hn5
    let v : {a : s.base.support // component s.base a = c} ≃ s.base.support :=
      Equiv.ofBijective Subtype.val ((Nat.bijective_iff_injective_and_card Subtype.val).mpr
        ⟨Subtype.val_injective, by omega⟩)
    let eA := v.symm.trans w
    have hcart (a b : s.base.support) :
        s.rootDatum.pairing a.val b.val = CartanMatrix.A 5 (eA a) (eA b) := by
      obtain ⟨a, rfl⟩ := v.surjective a
      obtain ⟨b, rfl⟩ := v.surjective b
      change s.rootDatum.pairing a.val.val b.val.val =
        CartanMatrix.A 5 (w (v.symm (v a))) (w (v.symm (v b)))
      simpa only [eA, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply] using
        hw (w a) (w b)
    exact s.not_isClosedSubgroup_of_typeA5_typeD5 q eA e hscD hcart hD f hf
  obtain ⟨r⟩ := nonempty_rootIndexEquiv_of_derived p s i hi
  have hd : Lie.dimension H = Lie.dimension p.torus.toGrp + Nat.card p.rootIndex :=
    p.isRootDatum.finrank_lie_eq_torus_add_card p.isConnectedReductive p.isSplitTorus p.isMaximalTorus
  have hcard' := (Nat.card_congr r).symm ▸ hcard
  omega

end Dimension

/-- A closed reductive subgroup of split simply connected D5 has no four
simple vertices with F4 Cartan entries. -/
theorem SplitPinning.not_has_typeF4_vertices_of_isClosedSubgroup_in_typeD5
    {k : Type u} [Field k] {A D : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom A.X.hom] [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
    (s : SplitPinning A) (q : SplitPinning D) (hscD : IsSimplyConnected D)
    (e : q.base.support ≃ Fin 5)
    (hD : ∀ a b, q.rootDatum.pairing a.val b.val = CartanMatrix.D 5 (e a) (e b))
    (f : A ⟶ D) (hf : IsClosedSubgroup f) (a : Fin 4 → s.base.support)
    (ha : Function.Injective a) :
    ¬ ∀ i j, s.rootDatum.pairing (a i).val (a j).val = CartanMatrix.F₄ i j := by
  intro hF
  let : IsAffineHom s.torus.toGrp.X.hom := s.isSplitTorus.isAffineHom
  let : IsAffineHom q.torus.toGrp.X.hom := q.isSplitTorus.isAffineHom
  let : q.rootDatum.IsReduced := q.isReduced
  have hAroots := Langlands.LinearAlgebra.card_root_ge_48_of_typeF4 s.rootDatum
    (fun i => (a i).val) (s.base.linearIndepOn_root.comp a ha) hF
  have hDroots := Langlands.LinearAlgebra.card_root_le_40_of_typeD5 q.rootDatum q.base e
    (fun i j => by simpa only [Equiv.apply_symm_apply] using hD (e.symm i) (e.symm j))
  have htorus : Lie.dimension q.torus.toGrp = 5 := by
    rw [q.torusDimension_eq_card_base_of_isSimplyConnected hscD, Nat.card_congr e, Nat.card_fin]
  have hA : Lie.dimension A = Lie.dimension s.torus.toGrp + Nat.card s.rootIndex :=
    s.isRootDatum.finrank_lie_eq_torus_add_card
    s.isConnectedReductive s.isSplitTorus s.isMaximalTorus
  have hD' : Lie.dimension D = Lie.dimension q.torus.toGrp + Nat.card q.rootIndex :=
    q.isRootDatum.finrank_lie_eq_torus_add_card
    q.isConnectedReductive q.isSplitTorus q.isMaximalTorus
  let : IsClosedImmersion f.hom.hom.left := hf
  let : Mono f.hom.hom := Over.mono_of_mono_left _
  have hdim : Lie.dimension A ≤ Lie.dimension D :=
    LinearMap.finrank_le_finrank_of_injective (Lie.targetMapLinear_injective f k)
  omega

section Cubic

variable {k K : Type u} [Field k] [CharZero k] [Field K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

omit [CharZero k] in
private theorem cartanConnected_iff_component_eq
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    (d : TitsIndexData H) (a b : d.Vertex) :
    d.CartanConnected a b ↔ component d.pinning.base a = component d.pinning.base b := by
  rw [component, component, Quotient.eq]
  change d.CartanConnected a b ↔
    Relation.EqvGen (fun x y : d.Vertex => d.cartan x y ≠ 0) a b
  let : IsEquiv d.Vertex (fun x y => d.CartanConnected x y) :=
    (Relation.EqvGen.is_equivalence (fun x y : d.Vertex => x ≠ y ∧ d.cartan x y ≠ 0)).isEquiv
  exact ⟨Relation.EqvGen.mono (fun _ _ h => h.2) a b,
    Relation.EqvGen.eqvGen_le (fun _ _ h => d.cartanConnected_of_cartan_ne_zero h) a b⟩

/-- Cubic splitting of anisotropic E6 forces a simply connected absolutely
almost-simple anisotropic factor of rank at most five with neither type A
nor type F4 over a finite separable extension of the ground field. -/
theorem IsAnisotropic.exists_nonTypeA_nonTypeF4_factor_of_typeE6_cubicSplit
    (hG : IsAnisotropic G) (hsc : IsSimplyConnected G) (hK : Module.finrank k K = 3)
    (p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (e : p.base.support ≃ Fin 6)
    (hE : ∀ a b, p.rootDatum.pairing a.val b.val = CartanMatrix.E 6 (e a) (e b)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L)
      (_ : Algebra.IsSeparable k L)
      (Q : GroupScheme (Spec (CommRingCat.of L))) (_ : IsAffineHom Q.X.hom)
      (_ : LocallyOfFiniteType Q.X.hom) (dQ : TitsIndexData Q),
        IsSimplyConnected Q ∧ IsAbsolutelyAlmostSimple Q ∧ IsAnisotropic Q ∧
        Nat.card dQ.Vertex ≤ 5 ∧
        (¬ ∃ n : ℕ, dQ.HasCartanMatrix (CartanMatrix.A n)) ∧
        ¬ dQ.HasCartanMatrix CartanMatrix.F₄ := by
  obtain ⟨H, j, hj, hH, hdim, A, i, hi, D, hDaff, l, hl, hA, hscD, q, f, hD⟩ :=
    hG.exists_typeE6_cubicSplit_largeSubgroup hsc hK p e hE
  let : IsAffineHom H.X.hom := hj.isAffineHom
  let : LocallyOfFiniteType H.X.hom := hj.locallyOfFiniteType
  let : Smooth H.X.hom := hH.smooth
  let : IsAffineHom A.X.hom := hi.1.isAffineHom
  let : LocallyOfFiniteType A.X.hom := hi.1.locallyOfFiniteType
  let : IsAffineHom D.X.hom := hDaff
  let : Smooth D.X.hom := hscD.isSemisimple.isConnectedReductive.smooth
  let E := SeparableClosure k
  let φ : K →ₐ[k] E := IsSepClosed.lift
  let : Algebra K E := φ.toRingHom.toAlgebra
  let : IsScalarTower k K E := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  let : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.tower_top (K := k) K
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap k E).injective
  let b := algebraBaseMap k E
  let B := GroupScheme.baseChange b
  let B' := GroupScheme.baseChange (algebraBaseMap K E)
  let GE := (GroupScheme.baseChange (algebraBaseMap k K) ⋙ B').obj G
  let HE := B.obj H
  have hHE := connectedReductiveFieldExtensionStatement k E H hH
  let : Smooth HE.X.hom := hHE.smooth
  obtain ⟨T, t, ht⟩ := maximalTorusExistence E HE
  obtain ⟨pH⟩ := splitPinningExistence E HE hHE T (toriAreSplit_of_isSepClosed E _ ht.1) t ht
  obtain ⟨d⟩ := titsIndexExistence k A hA
  let s := d.pinning.toSplitPinning
  let g := p.baseChange (F := E)
  let qE := q.baseChange (F := E)
  let eD := q.baseChangeNumbering (L := E) f
  have hDE := q.baseChangeNumbering_cartan (L := E) f hD
  have hscGE : IsSimplyConnected GE := isSimplyConnectedFieldExtension K E _
    (isSimplyConnectedFieldExtension k K G hsc)
  have hscDE := isSimplyConnectedFieldExtension K E D hscD
  let tG := GaloisPointComparison.towerBaseChangeIso k K E G
  let tA := GaloisPointComparison.towerBaseChangeIso k K E A
  let jE := B.map j ≫ tG.inv
  let lE := tA.inv ≫ B'.map l
  have hjE : IsClosedSubgroup jE := (hj.baseChange b).comp_iso tG.symm
  have hlE : IsClosedSubgroup lE := (hl.baseChange (algebraBaseMap K E)).iso_comp tA.symm
  have hiE := hi.baseChange_of_eq b (derivedSubgroup_baseChange_eq_of_field b H)
  have hg : Nat.card g.base.support = 6 :=
    (Nat.card_congr ((p.baseChangeSimpleEquiv (F := E)).symm.trans e)).trans (Nat.card_fin 6)
  have hrank : Nat.card s.base.support ≤ 5 := by
    let : IsAffineHom s.torus.toGrp.X.hom := s.isSplitTorus.isAffineHom
    let : IsAffineHom qE.torus.toGrp.X.hom := qE.isSplitTorus.isAffineHom
    have hq : Lie.dimension qE.torus.toGrp = 5 := by
      rw [qE.torusDimension_eq_card_base_of_isSimplyConnected hscDE, Nat.card_congr eD, Nat.card_fin]
    exact s.card_base_le_torusDimension.trans (hq ▸ (s.torusDimension_le_of_closedSubgroup qE lE hlE).1)
  have hnA : ∃ c : Component s.base, ¬ ∃ (n : ℕ)
      (w : {a : s.base.support // component s.base a = c} ≃ Fin n),
      ∀ a b, s.rootDatum.pairing (w.symm a).val.val (w.symm b).val.val = CartanMatrix.A n a b := by
    by_contra! hall
    have hbound := g.lieDimension_le_of_typeA_components_in_typeD5 pH s qE hscGE hg
      hscDE eD hDE jE hjE (B.map i) hiE lE hlE hall
    rw [lieDimension_baseChange H] at hbound
    omega
  obtain ⟨c, hc⟩ := hnA
  let a : d.Vertex := Quotient.out c
  have ha : component s.base a = c := Quotient.out_eq c
  let v : d.CartanComponent a ≃ {b : s.base.support // component s.base b = c} :=
    Equiv.subtypeEquivRight fun b => by
      rw [cartanConnected_iff_component_eq, show component d.pinning.base a = c from ha]
      exact eq_comm
  obtain ⟨C⟩ := semisimpleTitsComponentFactor k A d a
  let w := C.vertexEquiv.trans v
  have hAni : IsAnisotropic A := by
    change splitRank A = 0
    exact nonpos_iff_eq_zero.mp ((splitRank_le_of_isClosedSubgroup (i ≫ j) (hi.1.comp hj)).trans hG.le)
  refine ⟨C.extension, inferInstance, inferInstance, inferInstance, inferInstance,
    C.factor, inferInstance, inferInstance, C.index, C.simplyConnected, C.absolutelyAlmostSimple,
    C.anisotropic hAni, ?_, ?_, ?_⟩
  · exact (Nat.card_congr w).le.trans
      ((Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans hrank)
  · rintro ⟨n, u, hu⟩
    apply hc
    refine ⟨n, w.symm.trans u, fun i j => ?_⟩
    change d.cartan (C.vertexEquiv (u.symm i)).val (C.vertexEquiv (u.symm j)).val = _
    rw [C.cartan_eq]
    simpa only [Equiv.apply_symm_apply] using hu (u.symm i) (u.symm j)
  · rintro ⟨t, ht⟩
    let f₄ := w ∘ t.symm
    refine s.not_has_typeF4_vertices_of_isClosedSubgroup_in_typeD5 qE hscDE eD hDE lE hlE
      (fun i => (f₄ i).val) (Subtype.val_injective.comp (w.injective.comp t.symm.injective)) ?_
    intro i j
    change d.cartan (C.vertexEquiv (t.symm i)).val (C.vertexEquiv (t.symm j)).val = _
    rw [C.cartan_eq]
    simpa only [Equiv.apply_symm_apply] using ht (t.symm i) (t.symm j)

/-- Cubic splitting of anisotropic E6 forces a simply connected absolutely
almost-simple anisotropic factor of rank at most five outside type A over a
finite separable extension of the ground field. -/
theorem IsAnisotropic.exists_nonTypeA_factor_of_typeE6_cubicSplit
    (hG : IsAnisotropic G) (hsc : IsSimplyConnected G) (hK : Module.finrank k K = 3)
    (p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (e : p.base.support ≃ Fin 6)
    (hE : ∀ a b, p.rootDatum.pairing a.val b.val = CartanMatrix.E 6 (e a) (e b)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L)
      (_ : Algebra.IsSeparable k L)
      (Q : GroupScheme (Spec (CommRingCat.of L))) (_ : IsAffineHom Q.X.hom)
      (_ : LocallyOfFiniteType Q.X.hom) (dQ : TitsIndexData Q),
        IsSimplyConnected Q ∧ IsAbsolutelyAlmostSimple Q ∧ IsAnisotropic Q ∧
        Nat.card dQ.Vertex ≤ 5 ∧
        ¬ ∃ (n : ℕ) (v : dQ.Vertex ≃ Fin n), ∀ a b, dQ.cartan a b = CartanMatrix.A n (v a) (v b) := by
  obtain ⟨L, hL, hAlg, hFinite, hSep, Q, hAffine, hFT, d, hscQ, habs, hAni, hrank, hA, _⟩ :=
    hG.exists_nonTypeA_nonTypeF4_factor_of_typeE6_cubicSplit hsc hK p e hE
  exact ⟨L, hL, hAlg, hFinite, hSep, Q, hAffine, hFT, d, hscQ, habs, hAni, hrank, hA⟩

end Cubic

/-- An anisotropic E6 group split by a cubic Galois extension forces a
simply connected absolutely almost-simple anisotropic group outside type A
of rank at most five over a finite separable extension. -/
def TypeE6CubicSplitNonTypeAFactorStatement : Prop :=
  ∀ (k K : Type u) [Field k] [CharZero k] [Field K] [Algebra k K]
      [FiniteDimensional k K] [IsGalois k K], Module.finrank k K = 3 →
    ∀ (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
      [LocallyOfFiniteType G.X.hom], IsAnisotropic G → IsSimplyConnected G →
    ∀ (p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
      (e : p.base.support ≃ Fin 6),
      (∀ a b, p.rootDatum.pairing a.val b.val = CartanMatrix.E 6 (e a) (e b)) →
      ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L)
        (_ : Algebra.IsSeparable k L)
        (Q : GroupScheme (Spec (CommRingCat.of L))) (_ : IsAffineHom Q.X.hom)
        (_ : LocallyOfFiniteType Q.X.hom) (dQ : TitsIndexData Q),
          IsSimplyConnected Q ∧ IsAbsolutelyAlmostSimple Q ∧ IsAnisotropic Q ∧
          Nat.card dQ.Vertex ≤ 5 ∧
          ¬ ∃ (n : ℕ) (v : dQ.Vertex ≃ Fin n), ∀ a b, dQ.cartan a b = CartanMatrix.A n (v a) (v b)

theorem typeE6CubicSplitNonTypeAFactor : TypeE6CubicSplitNonTypeAFactorStatement.{u} := by
  intro k K _ _ _ _ _ _ hK G _ _ hG hsc p e hE
  exact hG.exists_nonTypeA_factor_of_typeE6_cubicSplit hsc hK p e hE

end Langlands.GroupScheme
