import Langlands.GroupScheme.Absolute.SemisimpleUnipotentCentralizerStatement
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.Unipotent.RationalPointsProof
import Langlands.GroupScheme.Reductive.CommutingMultiplication
import Langlands.GroupScheme.DominantHomFlatProof
import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.Rational.SplitSeriesExtension
import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.Order.OrderIsoNat

/-! # Connected centralizers in commutative unipotent normal subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace SemisimpleUnipotentCentralizer

private theorem eq_one_of_semisimple_mul_unipotent {k : Type u} [Field k] [PerfectField k]
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (a b : (Module.End k V)ˣ) (hc : Commute (b : Module.End k V) (a : Module.End k V))
    (ha : (a : Module.End k V).IsSemisimple)
    (hab : ((b : Module.End k V) * (a : Module.End k V)).IsSemisimple)
    (hb : IsNilpotent ((b : Module.End k V) - 1)) : b = 1 := by
  have hc' := hc.sub_left (Commute.one_left (a : Module.End k V))
  have he : ((b : Module.End k V) - 1) * (a : Module.End k V) + (a : Module.End k V) =
      0 + (b : Module.End k V) * (a : Module.End k V) := by
    rw [sub_mul, one_mul, sub_add_cancel, zero_add]
  have hzero : IsNilpotent (0 : Module.End k V) := ⟨1, by simp⟩
  have hz := (Module.End.isNilpotent_isSemisimple_unique (hc'.isNilpotent_mul_right hb)
    ha hzero hab (hc'.mul_left (Commute.refl _)) (Commute.zero_left _) he).1
  apply Units.ext
  change (b : Module.End k V) = 1
  apply sub_eq_zero.mp
  simpa only [mul_assoc, Units.mul_inv, mul_one, zero_mul] using
    congrArg (fun z : Module.End k V => z * ((a⁻¹ : (Module.End k V)ˣ) : Module.End k V)) hz

section Commutator

variable {S : Scheme.{u}} {G N : GroupScheme S} [IsCommMonObj N.X]
  (n : N ⟶ G) [Mono n.hom.hom] (hn : (SubgroupFunctor.range n).IsNormal)
  (s : Over.mk (𝟙 S) ⟶ G.X)

/-- The commutator with the section is multiplicative on the commutative normal subgroup. -/
private def commutator : N ⟶ N := by
  let a := LinearKernelTower.normalConjugation n hn
  letI : IsMonHom (a.commutatorMap s) := by
    apply Semidirect.isMonHom_of_mul_comp
    intro T x y
    simp only [a.commutatorMap_apply, a.act_mul_right, mul_inv_rev]
    ac_rfl
  exact Grp.homMk (a.commutatorMap s)

private theorem commutator_comp {T : Over S} (x : T ⟶ N.X) :
    (x ≫ (commutator n hn s).hom.hom) ≫ n.hom.hom =
      G.constantPoint s T * (x ≫ n.hom.hom) * (G.constantPoint s T)⁻¹ *
        (x ≫ n.hom.hom)⁻¹ := by
  change (x ≫ (LinearKernelTower.normalConjugation n hn).commutatorMap s) ≫ n.hom.hom = _
  rw [AutomorphicAction.commutatorMap_apply, MonObj.mul_comp, GrpObj.inv_comp,
    LinearKernelTower.normalConjugation_comp]

private theorem commutator_eq_one_iff {T : Over S} (x : T ⟶ N.X) :
    x ≫ (commutator n hn s).hom.hom = 1 ↔
      Commute (x ≫ n.hom.hom) (G.constantPoint s T) := by
  rw [← cancel_mono n.hom.hom, MonObj.one_comp, commutator_comp, mul_inv_eq_iff_eq_mul,
    one_mul, mul_inv_eq_iff_eq_mul]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

private theorem centralizer_eq_range_kernel :
    (G.pointCentralizer s).comap n = SubgroupFunctor.range (kernelι (commutator n hn s)) := by
  ext T x
  rw [SubgroupFunctor.mem_comap, G.mem_pointCentralizer, mem_range_kernelι_iff,
    commutator_eq_one_iff]
  rfl

end Commutator

section Field

variable {k : Type u} [Field k] [IsAlgClosed k]

private abbrev FieldGroup (k : Type u) [Field k] := GroupScheme (Spec (CommRingCat.of k))

private abbrev Point (X : Over (Spec (CommRingCat.of k))) :=
  Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X

private theorem commutator_eq_one_of_iterate_eq_one {G N : FieldGroup k}
    [IsCommMonObj N.X] [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    [LocallyOfFiniteType N.X.hom] [IsAffineHom N.X.hom]
    (n : N ⟶ G) [Mono n.hom.hom] (hn : (SubgroupFunctor.range n).IsNormal)
    (hN : IsUnipotent N) (s : Point G.X)
    (hs : ∀ (m : ℕ) (ρ : MatrixRepresentation G (Fin m)),
      Module.End.IsSemisimple (Matrix.toLin' (ρ.rationalMatrix s : Matrix (Fin m) (Fin m) k)))
    (x : Point N.X)
    (hd : (x ≫ (commutator n hn s).hom.hom) ≫ (commutator n hn s).hom.hom = 1) :
    x ≫ (commutator n hn s).hom.hom = 1 := by
  obtain ⟨m, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  let : Mono ρ.hom.hom := hρ.mono_overHom
  let y := x ≫ (commutator n hn s).hom.hom
  have hcomm : Commute (y ≫ n.hom.hom) s := by
    simpa only [GroupScheme.constantPoint_self] using (commutator_eq_one_iff n hn s y).mp hd
  have hconj : (y⁻¹ ≫ n.hom.hom) * s = (x ≫ n.hom.hom) * s * (x ≫ n.hom.hom)⁻¹ := by
    rw [GrpObj.inv_comp, show y ≫ n.hom.hom = _ by
      simpa only [GroupScheme.constantPoint_self] using commutator_comp n hn s x]
    simp [mul_assoc]
  let V := Fin m → k
  let L : Matrix (Fin m) (Fin m) k ≃ₐ[k] Module.End k V := Matrix.toLinAlgEquiv'
  let R : Point G.X →* (Module.End k V)ˣ := (Units.map L.toMonoidHom).comp ρ.rationalMatrix
  let a := R s
  let b := R (y⁻¹ ≫ n.hom.hom)
  let e : V ≃ₗ[k] V := LinearMap.GeneralLinearGroup.generalLinearEquiv k V (R (x ≫ n.hom.hom))
  have ha : (a : Module.End k V).IsSemisimple := hs m ρ
  have hab : ((b : Module.End k V) * (a : Module.End k V)).IsSemisimple := by
    refine (LinearEquiv.isSemisimple_iff (a : Module.End k V) _ e ?_).mp ha
    have hconj' : (y⁻¹ ≫ n.hom.hom) * s * (x ≫ n.hom.hom) = (x ≫ n.hom.hom) * s := by
      rw [hconj, inv_mul_cancel_right]
    change (R (x ≫ n.hom.hom) : Module.End k V) * (a : Module.End k V) =
      (b : Module.End k V) * (a : Module.End k V) * (R (x ≫ n.hom.hom) : Module.End k V)
    simpa only [map_mul, Units.val_mul] using
      (congrArg (fun p => (R p : Module.End k V)) hconj').symm
  have hb : IsNilpotent ((b : Module.End k V) - 1) := by
    have hnil := (perfectFieldUnipotentRationalPoints k N).1 hN
      (Fin m) (ρ.restrict n) y⁻¹
    rw [MatrixRepresentation.rationalMatrix_restrict] at hnil
    obtain ⟨l, hl⟩ := hnil
    refine ⟨l, ?_⟩
    change (L (ρ.rationalMatrix (y⁻¹ ≫ n.hom.hom) : Matrix (Fin m) (Fin m) k) - 1) ^ l = 0
    rw [← map_one L, ← map_sub, ← map_pow, hl, map_zero]
  have hcb : Commute (b : Module.End k V) (a : Module.End k V) := by
    dsimp only [a, b]
    rw [GrpObj.inv_comp]
    exact ((hcomm.inv_left.map R).map (Units.coeHom _))
  have he := eq_one_of_semisimple_mul_unipotent a b hcb ha hab hb
  have hy : y⁻¹ ≫ n.hom.hom = 1 := by
    apply ρ.rationalMatrix_injective
    apply Units.ext
    apply L.injective
    have he' : (b : Module.End k V) = 1 := by rw [he, Units.val_one]
    change L (ρ.rationalMatrix (y⁻¹ ≫ n.hom.hom) : Matrix (Fin m) (Fin m) k) = 1 at he'
    rw [map_one ρ.rationalMatrix, Units.val_one, map_one]
    exact he'
  apply inv_eq_one.mp
  apply (cancel_mono n.hom.hom).mp
  simpa only [MonObj.one_comp] using hy

/-- A rational point in the image of an open subset has a rational lift in that subset. -/
private theorem lift_point_in_open
    {X Y : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (U : Set X.left) (hU : IsOpen U) (y : Point Y)
    (hy : y.left (IsLocalRing.closedPoint k) ∈ f.left '' U) :
    ∃ x : Point X, x.left (IsLocalRing.closedPoint k) ∈ U ∧ x ≫ f = y := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  let z := y.left (IsLocalRing.closedPoint k)
  have hz : IsClosed ({z} : Set Y.left) :=
    ((pointEquivClosedPoint Y.hom) ⟨y.left, y.w⟩).property
  obtain ⟨w, hw, hfw⟩ := hy
  have hloc : IsLocallyClosed (U ∩ f.left ⁻¹' {z}) :=
    hU.isLocallyClosed.inter (hz.preimage f.left.continuous).isLocallyClosed
  have hne : (U ∩ f.left ⁻¹' {z}).Nonempty := ⟨w, hw, hfw⟩
  obtain ⟨v, hv, hvc⟩ := nonempty_inter_closedPoints hne hloc
  let x : Point X := Over.homMk (pointOfClosedPoint X.hom v hvc) (by simp)
  refine ⟨x, ?_, Over.OverMorphism.ext ?_⟩
  · change pointOfClosedPoint X.hom v hvc _ ∈ U
    simpa only [pointOfClosedPoint_apply] using hv.1
  · apply ext_of_apply_closedPoint_eq Y.hom (x ≫ f).w y.w
    change f.left (pointOfClosedPoint X.hom v hvc _) = z
    rw [pointOfClosedPoint_apply]
    exact hv.2

omit [IsAlgClosed k] in
private theorem isClosed_range_of_smooth_connected
    {H : FieldGroup k} [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (δ : H ⟶ H) : IsClosed (Set.range δ.hom.hom.left) := by
  obtain ⟨M, j, q, hj, hfac, _, hsurj, _⟩ := HomImage.exists_image δ
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Surjective q.hom.hom.left := hsurj
  rw [← hfac, Grp.comp_hom_hom, Over.comp_left]
  change IsClosed (Set.range (j.hom.hom.left ∘ q.hom.hom.left))
  rw [Set.range_comp, q.hom.hom.left.surjective.range_eq, Set.image_univ]
  exact j.hom.hom.left.isClosedEmbedding.isClosed_range

omit [IsAlgClosed k] in
private theorem injective_on_rational_image {H : FieldGroup k} (δ : H ⟶ H)
    (hker : ∀ x : Point H.X, (x ≫ δ.hom.hom) ≫ δ.hom.hom = 1 → x ≫ δ.hom.hom = 1) :
    Set.InjOn (fun x : Point H.X => x ≫ δ.hom.hom) (Set.range fun x : Point H.X => x ≫ δ.hom.hom) := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ he
  change (a ≫ δ.hom.hom) ≫ δ.hom.hom = (b ≫ δ.hom.hom) ≫ δ.hom.hom at he
  apply div_eq_one.mp
  have h : ((a / b) ≫ δ.hom.hom) ≫ δ.hom.hom = 1 := by
    rw [GrpObj.div_comp, GrpObj.div_comp, he, div_self']
  simpa only [GrpObj.div_comp] using hker (a / b) h

/-- Stabilization of the closed iterated images makes the commutator
surjective on its rational image once it is injective there. -/
private theorem exists_comp_comp_eq_comp
    {H : FieldGroup k} [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (δ : H ⟶ H)
    (hker : ∀ x : Point H.X, (x ≫ δ.hom.hom) ≫ δ.hom.hom = 1 → x ≫ δ.hom.hom = 1)
    (x : Point H.X) : ∃ y : Point H.X, (y ≫ δ.hom.hom) ≫ δ.hom.hom = x ≫ δ.hom.hom := by
  let α : Point H.X → Point H.X := fun x => x ≫ δ.hom.hom
  have hinj : Set.InjOn α (Set.range α) := injective_on_rational_image δ hker
  let d : End H := End.of δ
  let F (i : ℕ) : Closeds H.X.left :=
    ⟨Set.range (d ^ i).asHom.hom.hom.left, isClosed_range_of_smooth_connected _⟩
  have hF : Antitone F := antitone_nat_of_succ_le fun i => by
    change Set.range (d ^ (i + 1)).asHom.hom.hom.left ⊆ Set.range (d ^ i).asHom.hom.hom.left
    rw [pow_succ, End.mul_asHom, Grp.comp_hom_hom, Over.comp_left]
    rintro _ ⟨z, rfl⟩
    exact ⟨δ.hom.hom.left z, rfl⟩
  have : IsLocallyNoetherian H.X.left := LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : AlgebraicGeometry.IsNoetherian H.X.left := ⟨⟩
  obtain ⟨i, hi⟩ := WellFoundedLT.antitone_chain_condition hF
  have he : F (i + 1) = F (i + 2) := (hi _ (by omega)).symm.trans (hi _ (by omega))
  let p := x ≫ (d ^ (i + 1)).asHom.hom.hom
  have hp : p.left (IsLocalRing.closedPoint k) ∈ (F (i + 2) : Set H.X.left) := by
    rw [← he]
    exact ⟨x.left (IsLocalRing.closedPoint k), rfl⟩
  let f := (d ^ (i + 2)).asHom.hom.hom
  obtain ⟨y, _, hy⟩ := lift_point_in_open f Set.univ isOpen_univ p
    (show p.left (IsLocalRing.closedPoint k) ∈ f.left '' Set.univ by
      rw [Set.image_univ]
      exact hp)
  have hiterate (m : ℕ) (z : Point H.X) : z ≫ (d ^ m).asHom.hom.hom = α^[m] z := by
    induction m with
    | zero => simp
    | succ m hm =>
      rw [pow_succ', End.mul_asHom, Grp.comp_hom_hom, ← Category.assoc, hm,
        Function.iterate_succ_apply']
  have hy' : α^[i] (α (α y)) = α^[i] (α x) := by
    change y ≫ (d ^ (i + 2)).asHom.hom.hom = x ≫ (d ^ (i + 1)).asHom.hom.hom at hy
    rw [hiterate, hiterate, Function.iterate_succ_apply (n := i + 1),
      Function.iterate_succ_apply (n := i), Function.iterate_succ_apply (n := i)] at hy
    exact hy
  exact ⟨y, hinj.iterate (fun z _ => Set.mem_range_self z) i
    (Set.mem_range_self (α y)) (Set.mem_range_self x) hy'⟩

/-- If the projection is well-defined on every rational fiber of an open
surjection, a clopen separation of the projection's target descends. -/
private theorem connected_of_unique_projection
    {X Y Z : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] [ConnectedSpace Y.left]
    (f : X ⟶ Y) (p : X ⟶ Z) (hf : IsOpenMap f.left)
    (hs : Function.Surjective f.left) (hp : Function.Surjective p.left)
    (huniq : ∀ {q q' : Point X}, q ≫ f = q' ≫ f → q ≫ p = q' ≫ p) :
    ConnectedSpace Z.left := by
  have : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  obtain ⟨z⟩ := (inferInstance : Nonempty Y.left)
  obtain ⟨w, _⟩ := hs z
  refine connectedSpace_iff_clopen.mpr ⟨⟨p.left w⟩, fun U hU => ?_⟩
  by_contra! hnontrivial
  let A := f.left '' (p.left ⁻¹' U)
  let B := f.left '' (p.left ⁻¹' Uᶜ)
  have ha := hU.isOpen.preimage p.left.continuous
  have hb := hU.isClosed.isOpen_compl.preimage p.left.continuous
  have hA : IsOpen A := hf _ ha
  have hB : IsOpen B := hf _ hb
  have hcover : (Set.univ : Set Y.left) ⊆ A ∪ B := by
    intro y _
    obtain ⟨v, rfl⟩ := hs y
    by_cases hv : p.left v ∈ U
    · exact Or.inl ⟨v, hv, rfl⟩
    · exact Or.inr ⟨v, hv, rfl⟩
  have hnonemptyA : A.Nonempty := (hnontrivial.1.preimage hp).image _
  have hnonemptyB : B.Nonempty := ((Set.nonempty_compl.mpr hnontrivial.2).preimage hp).image _
  have hoverlap : (A ∩ B).Nonempty := by
    simpa only [Set.univ_inter] using
      (isPreconnected_univ A B hA hB hcover (by simpa using hnonemptyA)
        (by simpa using hnonemptyB))
  obtain ⟨v, hv, hvc⟩ := nonempty_inter_closedPoints hoverlap (hA.inter hB).isLocallyClosed
  let y : Point Y := Over.homMk (pointOfClosedPoint Y.hom v hvc) (by simp)
  have hy : y.left (IsLocalRing.closedPoint k) = v :=
    pointOfClosedPoint_apply Y.hom v hvc _
  obtain ⟨q, hq, hqf⟩ := lift_point_in_open f _ ha y (by rw [hy]; exact hv.1)
  obtain ⟨q', hq', hq'f⟩ := lift_point_in_open f _ hb y (by rw [hy]; exact hv.2)
  have h := congrArg (fun g : Point Z => g.left (IsLocalRing.closedPoint k))
    (huniq (hqf.trans hq'f.symm))
  exact hq' (h ▸ hq)

end Field

end SemisimpleUnipotentCentralizer

open SemisimpleUnipotentCentralizer in
/-- Milne, Lemma 16.39. The fixed subgroup is connected and its product with
the image of the commutator covers the commutative unipotent subgroup. -/
theorem semisimpleUnipotentCentralizer : SemisimpleUnipotentCentralizerStatement.{u} := by
  intro k _ _ G N _ _ _ _ _ _ n hn hN hu s hs C c hc
  let : Mono n.hom.hom := hn.mono_overHom
  let : Mono c.hom.hom := hc.1
  let : IsAffineHom N.X.hom := hn.isAffineHom
  let δ := commutator n hN s
  have hr : SubgroupFunctor.range c = SubgroupFunctor.range (kernelι δ) :=
    hc.2.trans (centralizer_eq_range_kernel n hN s)
  have hcc : IsClosedSubgroup c :=
    RelativeRoot.IsClosedSubgroup.of_range_eq (kernelι_isClosedImmersion δ) hr
  have : IsClosedImmersion c.hom.hom.left := hcc
  have : LocallyOfFiniteType C.X.hom := by
    rw [← Over.w c.hom.hom]
    infer_instance
  have : IsAffineHom C.X.hom := hcc.isAffineHom
  have hδ : ∀ x : Point N.X, (x ≫ δ.hom.hom) ≫ δ.hom.hom = 1 → x ≫ δ.hom.hom = 1 :=
    commutator_eq_one_of_iterate_eq_one n hN hu s hs
  have hcomm : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ N.X) (y : T ⟶ C.X),
      Commute (x ≫ δ.hom.hom) (y ≫ c.hom.hom) := fun _ _ _ => Commute.all _ _
  let f := commutingSubgroupMultiplicationHom δ c hcomm
  let p := snd N.X C.X
  have hf (T : Over (Spec (CommRingCat.of k))) (q : T ⟶ N.X ⊗ C.X) :
      q ≫ f.hom.hom = ((q ≫ fst N.X C.X) ≫ δ.hom.hom) * ((q ≫ p) ≫ c.hom.hom) := by
    change q ≫ subgroupMultiplication δ c = _
    simp only [subgroupMultiplication, MonObj.comp_mul, Category.assoc, p]
  have hker {x : Point N.X} : (∃ y : Point C.X, y ≫ c.hom.hom = x) ↔ x ≫ δ.hom.hom = 1 := by
    rw [← SubgroupFunctor.mem_range, hr, mem_range_kernelι_iff]
  have hcover (z : Point N.X) : ∃ q : Point (N.X ⊗ C.X), q ≫ f.hom.hom = z := by
    obtain ⟨x, hx⟩ := exists_comp_comp_eq_comp δ hδ z
    have he : ((x ≫ δ.hom.hom)⁻¹ * z) ≫ δ.hom.hom = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hx, inv_mul_cancel]
    obtain ⟨y, hy⟩ := hker.mpr he
    refine ⟨lift x y, ?_⟩
    rw [hf, lift_fst, show lift x y ≫ p = y from lift_snd x y, hy, mul_inv_cancel_left]
  have huniq {q q' : Point (N.X ⊗ C.X)}
      (he : q ≫ f.hom.hom = q' ≫ f.hom.hom) : q ≫ p = q' ≫ p := by
    let x := q ≫ fst N.X C.X
    let x' := q' ≫ fst N.X C.X
    let y := (q ≫ p) ≫ c.hom.hom
    let y' := (q' ≫ p) ≫ c.hom.hom
    have hy : y ≫ δ.hom.hom = 1 := hker.mp ⟨q ≫ p, rfl⟩
    have hy' : y' ≫ δ.hom.hom = 1 := hker.mp ⟨q' ≫ p, rfl⟩
    have he' : (x ≫ δ.hom.hom) * y = (x' ≫ δ.hom.hom) * y' := (hf _ q).symm.trans
      (he.trans (hf _ q'))
    have hdiff := congrArg (fun t : Point N.X => t ≫ δ.hom.hom) he'
    rw [MonObj.mul_comp, MonObj.mul_comp, hy, hy', mul_one, mul_one] at hdiff
    have hcancel : (x ≫ δ.hom.hom) = (x' ≫ δ.hom.hom) := by
      exact injective_on_rational_image δ hδ (Set.mem_range_self x) (Set.mem_range_self x') hdiff
    rw [hcancel] at he'
    exact (cancel_mono c.hom.hom).mp (mul_left_cancel he')
  have : LocallyOfFiniteType (N ⊗ C).X.hom := by
    change LocallyOfFiniteType (CategoryTheory.Limits.pullback.fst N.X.hom C.X.hom ≫ N.X.hom)
    infer_instance
  have : QuasiCompact (N ⊗ C).X.hom := by
    change QuasiCompact (CategoryTheory.Limits.pullback.fst N.X.hom C.X.hom ≫ N.X.hom)
    infer_instance
  have : JacobsonSpace N.X.left := LocallyOfFiniteType.jacobsonSpace N.X.hom
  have : IsDominant f.hom.hom.left := by
    refine ⟨Dense.mono (fun y hy => ?_) (dense_iff_closure_eq.mpr closure_closedPoints)⟩
    let z : Point N.X := Over.homMk (pointOfClosedPoint N.X.hom y hy) (by simp)
    obtain ⟨q, hq⟩ := hcover z
    refine ⟨q.left (IsLocalRing.closedPoint k), ?_⟩
    have he := congrArg (fun t : Point N.X => t.left (IsLocalRing.closedPoint k)) hq
    change f.hom.hom.left (q.left (IsLocalRing.closedPoint k)) =
      pointOfClosedPoint N.X.hom y hy (IsLocalRing.closedPoint k) at he
    rwa [pointOfClosedPoint_apply] at he
  have : IsReduced N.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k N.X.left N.X.hom
  obtain ⟨hflat, hsurj, _⟩ := dominantGroupHomFlat k (N ⊗ C) N f
  have : Flat f.hom.hom.left := hflat
  have : Surjective f.hom.hom.left := hsurj
  have : LocallyOfFiniteType f.hom.hom.left := by
    have : LocallyOfFiniteType (f.hom.hom.left ≫ N.X.hom) := by
      rw [Over.w f.hom.hom]
      infer_instance
    exact locallyOfFiniteType_of_comp _ N.X.hom
  have : IsLocallyNoetherian N.X.left := LocallyOfFiniteType.isLocallyNoetherian N.X.hom
  have hp : Function.Surjective p.left := by
    intro y
    refine ⟨(lift (1 : C.X ⟶ N.X) (𝟙 C.X)).left y, ?_⟩
    have he : lift (1 : C.X ⟶ N.X) (𝟙 C.X) ≫ p = 𝟙 C.X := lift_snd _ _
    exact congrArg (fun t : C.X ⟶ C.X => t.left y) he
  exact ⟨connected_of_unique_projection f.hom.hom p f.hom.hom.left.isOpenMap
    f.hom.hom.left.surjective hp huniq, hsurj⟩

end Langlands.GroupScheme
