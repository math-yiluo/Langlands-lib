import Langlands.GroupScheme.Derived.CentralSplitTorusFactorization
import Langlands.GroupScheme.Rational.WeylTorusNorm
import Langlands.GroupScheme.Torus.CommutatorEnd
import Langlands.GroupScheme.Torus.SplitMultiplication
import Langlands.GroupScheme.Rational.ReductiveWeylFaithfulness
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Surjectivity of supplied split factors from a central Weyl norm -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

section Complement

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- Every Weyl translate differs from the identity by an actual derived-valued map. -/
theorem relativeWeylTorusAction_sub_id_eval_mem_derived
    (w : relativeWeylGroup i) (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ T.X) :
    (x ≫ (CommGroupScheme.groupHom ((relativeWeylTorusAction i w).hom - 𝟙 T)).hom.hom) ≫
      i.hom.hom ∈ (derivedSubgroup G).carrier U := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  change (x ≫ (CommGroupScheme.groupHom (torusCommutatorEnd i n)).hom.hom) ≫
    i.hom.hom ∈ (derivedSubgroup G).carrier U
  rw [Category.assoc, comp_torusCommutatorEnd]
  exact derivedSubgroup_containsCommutators G U (G.constantPoint n.val U) (x ≫ i.hom.hom)

variable [Fintype (relativeWeylGroup i)]

/-- The integral complement of the norm, as a sum of actual endomorphisms. -/
def relativeWeylTorusComplement : T ⟶ T :=
  ∑ w : relativeWeylGroup i, (𝟙 T - (relativeWeylTorusAction i w).hom)

/-- Complement and norm sum to the nonzero group-order multiple of the identity. -/
theorem relativeWeylTorusComplement_add_norm :
    relativeWeylTorusComplement i + relativeWeylTorusNorm i =
      (Fintype.card (relativeWeylGroup i) : ℤ) • 𝟙 T := by
  rw [relativeWeylTorusComplement, relativeWeylTorusNorm, ← Finset.sum_add_distrib]
  simp

/-- The complement has image in the actual derived subgroup on every test scheme. -/
theorem relativeWeylTorusComplement_eval_mem_derived
    (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ T.X) :
    x ≫ (CommGroupScheme.groupHom (relativeWeylTorusComplement i) ≫ i).hom.hom ∈
      (derivedSubgroup G).carrier U := by
  change x ≫ (CommGroupScheme.groupHom (relativeWeylTorusComplement i)).hom.hom ∈
    ((derivedSubgroup G).comap i).carrier U
  rw [relativeWeylTorusComplement, comp_groupHom_sum]
  apply Subgroup.prod_mem
  intro w _
  have hw := relativeWeylTorusAction_sub_id_eval_mem_derived i w U x
  change x ≫ (CommGroupScheme.groupHom ((relativeWeylTorusAction i w).hom - 𝟙 T)).hom.hom ∈
    ((derivedSubgroup G).comap i).carrier U at hw
  rw [← neg_sub ((relativeWeylTorusAction i w).hom) (𝟙 T)]
  have hneg := congrArg Additive.toMul
    ((evalPoint x).map_neg ((relativeWeylTorusAction i w).hom - 𝟙 T))
  change x ≫ (CommGroupScheme.groupHom (-((relativeWeylTorusAction i w).hom - 𝟙 T))).hom.hom =
    (x ≫ (CommGroupScheme.groupHom ((relativeWeylTorusAction i w).hom - 𝟙 T)).hom.hom)⁻¹ at hneg
  rw [hneg]
  exact Subgroup.inv_mem _ hw

end Complement

section PowerFactor

variable {k : Type u} [Field k]
    {G D : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]
    {S S_D A : CommGroupScheme (Spec (CommRingCat.of k))}
    {d : D ⟶ G} {i : S.toGrp ⟶ G} {j : S_D.toGrp ⟶ D}
    {e : S_D ⟶ S} {a : A.toGrp ⟶ G} {c : A ⟶ S}

/-- A derived-valued part and a central part of an integer multiple of the
identity give a factorization of that power map through the supplied product. -/
theorem exists_splitProduct_powerFactor_of_central_complement
    (hd : IsDerivedSubgroup d) (hi : IsSplitSubtorus i)
    (hj : IsMaximalSplitTorus j)
    (he : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (ha : IsSplitComponent a) (hc : CommGroupScheme.groupHom c ≫ i = a)
    (q r : S ⟶ S) (n : ℤ) (hqr : q + r = n • 𝟙 S)
    (hq : ∀ (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ S.X),
      x ≫ (CommGroupScheme.groupHom q ≫ i).hom.hom ∈ (derivedSubgroup G).carrier U)
    (hr : IsCentral (CommGroupScheme.groupHom r ≫ i)) :
    ∃ l : S.toGrp ⟶ S_D.toGrp ⊗ A.toGrp,
      l ≫ prodHom (CommGroupScheme.groupHom e) (CommGroupScheme.groupHom c)
        (fun _ _ _ => Commute.all _ _) = multiplication S.toGrp n := by
  obtain ⟨f, hf⟩ := hd.exists_factor_splitTorusEnd hi hj he q hq
  obtain ⟨g, hg⟩ := ha.exists_factor hi.1 hr
  have : IsClosedImmersion i.hom.hom.left := hi.2
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have hgc : g ≫ CommGroupScheme.groupHom c = CommGroupScheme.groupHom r := by
    apply Grp.hom_ext
    apply (cancel_mono i.hom.hom).mp
    have h : (g ≫ CommGroupScheme.groupHom c) ≫ i =
        CommGroupScheme.groupHom r ≫ i := by
      rw [Category.assoc, hc, hg]
    exact congrArg (fun z => z.hom.hom) h
  have hfe : CommGroupScheme.groupHom f ≫ CommGroupScheme.groupHom e =
      CommGroupScheme.groupHom q := congrArg CommGroupScheme.groupHom hf
  let l : S.toGrp ⟶ S_D.toGrp ⊗ A.toGrp := lift (CommGroupScheme.groupHom f) g
  refine ⟨l, ?_⟩
  apply hom_ext_points
  intro U x
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_prodHom]
  simp only [l, productPointsEquiv_fst, productPointsEquiv_snd, Grp.lift_hom,
    Mon.lift_hom, Category.assoc, lift_fst, lift_snd]
  have hxf : (x ≫ (CommGroupScheme.groupHom f).hom.hom) ≫
      (CommGroupScheme.groupHom e).hom.hom =
      x ≫ (CommGroupScheme.groupHom q).hom.hom := by
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun z => x ≫ z.hom.hom) hfe
  have hxg : (x ≫ g.hom.hom) ≫ (CommGroupScheme.groupHom c).hom.hom =
      x ≫ (CommGroupScheme.groupHom r).hom.hom := by
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun z => x ≫ z.hom.hom) hgc
  rw [← Category.assoc, ← Category.assoc, hxf, hxg, ← comp_groupHom_add, hqr,
    comp_groupHom_zsmul, points_multiplication]
  rfl

/-- A nonzero power-map factorization gives scheme surjectivity of the product. -/
theorem splitProduct_surjective_of_central_complement
    (hd : IsDerivedSubgroup d) (hi : IsSplitSubtorus i)
    (hj : IsMaximalSplitTorus j)
    (he : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (ha : IsSplitComponent a) (hc : CommGroupScheme.groupHom c ≫ i = a)
    (q r : S ⟶ S) (n : ℤ) (hn : n ≠ 0) (hqr : q + r = n • 𝟙 S)
    (hq : ∀ (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ S.X),
      x ≫ (CommGroupScheme.groupHom q ≫ i).hom.hom ∈ (derivedSubgroup G).carrier U)
    (hr : IsCentral (CommGroupScheme.groupHom r ≫ i)) :
    Surjective (prodHom (CommGroupScheme.groupHom e) (CommGroupScheme.groupHom c)
      (fun _ _ _ => Commute.all _ _)).hom.hom.left := by
  obtain ⟨l, hl⟩ := exists_splitProduct_powerFactor_of_central_complement
    hd hi hj he ha hc q r n hqr hq hr
  let p := prodHom (CommGroupScheme.groupHom e) (CommGroupScheme.groupHom c)
    (fun _ _ _ => Commute.all _ _)
  have : Surjective (multiplication S.toGrp n).hom.hom.left :=
    (hi.1.flat_and_surjective_multiplication hn).2
  have : Surjective (l.hom.hom.left ≫ p.hom.hom.left) := by
    change Surjective (l ≫ p).hom.hom.left
    rw [hl]
    infer_instance
  exact Surjective.of_comp l.hom.hom.left p.hom.hom.left

/-- Centrality of the actual Weyl norm implies scheme surjectivity of the
supplied derived and central split factors. -/
theorem splitProduct_surjective_of_central_weyl_norm
    [Mono i.hom.hom.left] [Fintype (relativeWeylGroup i)]
    (hd : IsDerivedSubgroup d) (hi : IsSplitSubtorus i)
    (hj : IsMaximalSplitTorus j)
    (he : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (ha : IsSplitComponent a) (hc : CommGroupScheme.groupHom c ≫ i = a)
    (hnorm : IsCentral (CommGroupScheme.groupHom (relativeWeylTorusNorm i) ≫ i)) :
    Surjective (prodHom (CommGroupScheme.groupHom e) (CommGroupScheme.groupHom c)
      (fun _ _ _ => Commute.all _ _)).hom.hom.left := by
  have hn : (Fintype.card (relativeWeylGroup i) : ℤ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (relativeWeylGroup i) ≠ 0)
  exact splitProduct_surjective_of_central_complement hd hi hj he ha hc
    (relativeWeylTorusComplement i) (relativeWeylTorusNorm i)
    (Fintype.card (relativeWeylGroup i)) hn
    (relativeWeylTorusComplement_add_norm i)
    (relativeWeylTorusComplement_eval_mem_derived i) hnorm

end PowerFactor

section Reflections

variable {k : Type u} [Field k]
    {G D : GroupScheme (Spec (CommRingCat.of k))}
    {S S_D A : CommGroupScheme (Spec (CommRingCat.of k))}
    {d : D ⟶ G} {i : S.toGrp ⟶ G} {j : S_D.toGrp ⟶ D}
    {e : S_D ⟶ S} {a : A.toGrp ⟶ G} {c : A ⟶ S}

/-- Actual root reflections suffice for the supplied product's surjectivity;
reflection existence is an explicit remaining structural premise. -/
theorem splitProduct_surjective_of_relative_reflections
    (hG : IsConnectedReductive G) (hd : IsDerivedSubgroup d)
    (hi : IsMaximalSplitTorus i) (hj : IsMaximalSplitTorus j)
    (he : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (ha : IsSplitComponent a) (hc : CommGroupScheme.groupHom c ≫ i = a)
    (href : have : IsAffineHom G.X.hom := hG.isAffineHom
      have : Mono i.hom.hom.left := hi.1.mono
      ∀ α ∈ relativeRoots i, ∃ w, IsRelativeReflection i α w) :
    Surjective (prodHom (CommGroupScheme.groupHom e) (CommGroupScheme.groupHom c)
      (fun _ _ _ => Commute.all _ _)).hom.hom.left := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : Mono i.hom.hom.left := hi.1.mono
  have : Finite (relativeWeylGroup i) := hG.finite_relativeWeylGroup i hi
  let : Fintype (relativeWeylGroup i) := Fintype.ofFinite _
  exact splitProduct_surjective_of_central_weyl_norm hd hi.1 hj he ha hc
    (relativeWeylTorusNorm_isCentral i hi.1.1 href)

end Reflections

end Langlands.GroupScheme
