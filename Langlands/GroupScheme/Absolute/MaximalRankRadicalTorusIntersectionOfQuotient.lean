import Langlands.GroupScheme.Absolute.MaximalRankRadicalTorusIntersectionOfComplement
import Langlands.GroupScheme.Absolute.SolvableSplitExtensionOneDimensional
import Langlands.GroupScheme.Absolute.TriangularTorusConjugacy
import Langlands.GroupScheme.Absolute.NormalUnipotentBorelContainmentProof
import Langlands.GroupScheme.Absolute.ParabolicBorelFactorization
import Langlands.GroupScheme.SubgroupFunctor.SmoothConnectedNormalProductExistenceProof
import Langlands.AbelianScheme.AlgClosedIsogenyPointLifting

/-! # Radical torus intersections from the solvable torus quotient

The maximal torus `T` of `H` normalizes the solvable radical `R`, so the two generate a smooth
connected closed subgroup `P = R · T` of `H`. Over an algebraically closed field `P` is solvable,
so its maximal tori are conjugate by the solvable conjugacy theorem, and the intersection of `T`
with `R` is computed inside `P`. This removes the conjugacy of maximal tori in `H` from the
premises of `maximalRankRadicalTorusIntersectionStatement_of_complement`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-! ### The chosen smooth connected product -/

namespace SubgroupFunctor

variable {k : Type u} [Field k] {G H N : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [Smooth H.X.hom] [Smooth N.X.hom] [ConnectedSpace H.X.left] [ConnectedSpace N.X.left]
  (i : H ⟶ G) (j : N ⟶ G) (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j)
  (hn : (range i).IsNormalizedBy (range j))

/-- A chosen smooth connected group scheme representing the fppf-local product `H · N` of two
smooth connected closed subgroups of an affine algebraic group, the second normalizing the
first; it exists by `exists_smoothConnected_fppfProduct`. -/
def smoothConnectedProduct : GroupScheme (Spec (CommRingCat.of k)) :=
  Classical.choose (exists_smoothConnected_fppfProduct i j hi hj hn)

/-- The closed inclusion of the chosen smooth connected product `H · N` into `G`. -/
def smoothConnectedProductι : smoothConnectedProduct i j hi hj hn ⟶ G :=
  Classical.choose (Classical.choose_spec (exists_smoothConnected_fppfProduct i j hi hj hn))

/-- The chosen product represents the fppf-local product and is smooth and connected. -/
theorem smoothConnectedProductι_spec :
    IsFppfProduct (range i) (range j) (smoothConnectedProductι i j hi hj hn) ∧
      Smooth (smoothConnectedProduct i j hi hj hn).X.hom ∧
        ConnectedSpace (smoothConnectedProduct i j hi hj hn).X.left :=
  Classical.choose_spec (Classical.choose_spec (exists_smoothConnected_fppfProduct i j hi hj hn))

end SubgroupFunctor

/-! ### Solvability of the product -/

section AlgebraicallyClosed

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Over an algebraically closed field, every rational point of a represented fppf-local
product is an actual product of rational points of the two factors: the flat cover of the
point has a rational point. -/
theorem SubgroupFunctor.IsFppfProduct.exists_mul_of_rationalPoint
    {G P : GroupScheme (Spec (CommRingCat.of k))} {F N : SubgroupFunctor G} {p : P ⟶ G}
    (hp : SubgroupFunctor.IsFppfProduct F N p)
    {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hx : x ∈ (SubgroupFunctor.range p).carrier _) :
    ∃ a b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      a ∈ F.carrier _ ∧ b ∈ N.carrier _ ∧ x = a * b := by
  obtain ⟨V, v, -, hs, hl, a, b, ha, hb, he⟩ := (hp.mem_range_iff _ x).1 hx
  have : Surjective v.left := hs
  have : LocallyOfFinitePresentation v.left := hl
  obtain ⟨c, hc⟩ := exists_point_lift_of_locallyOfFiniteType_surjective (K := k) v.left
    (𝟙 (Spec (CommRingCat.of k)))
  let e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ V := Over.homMk c (by
    rw [← Over.w v, ← Category.assoc, hc]
    rfl)
  have hev : e ≫ v = 𝟙 _ := by
    ext
    exact hc
  refine ⟨e ≫ a, e ≫ b, F.comp_mem e ha, N.comp_mem e hb, ?_⟩
  rw [← MonObj.comp_mul, ← he, ← Category.assoc, hev, Category.id_comp]

/-- Over an algebraically closed field, the represented fppf-local product of a solvable normal
subgroup `R` and a solvable subgroup `N` is solvable: its rational points lie in the product of
the rational points of the two factors. -/
theorem SubgroupFunctor.IsFppfProduct.isSolvableGroupScheme
    {G P R N : GroupScheme (Spec (CommRingCat.of k))} {r : R ⟶ G} {n : N ⟶ G} {p : P ⟶ G}
    (hp : SubgroupFunctor.IsFppfProduct (SubgroupFunctor.range r) (SubgroupFunctor.range n) p)
    (hr : (SubgroupFunctor.range r).IsNormal)
    (hR : IsSolvableGroupScheme R) (hN : IsSolvableGroupScheme N) :
    IsSolvableGroupScheme P := by
  rw [isSolvableGroupScheme_iff_rationalPoints] at hR hN ⊢
  let pt := Over.mk (𝟙 (Spec (CommRingCat.of k)))
  let φr := IsMonHom.monoidHom r.hom.hom pt
  let φn := IsMonHom.monoidHom n.hom.hom pt
  let φ := IsMonHom.monoidHom p.hom.hom pt
  let A := φr.range
  let B := φn.range
  have hA : ∀ x, x ∈ A ↔ x ∈ (SubgroupFunctor.range r).carrier pt := fun _ => Iff.rfl
  have hB : ∀ x, x ∈ B ↔ x ∈ (SubgroupFunctor.range n).carrier pt := fun _ => Iff.rfl
  have : A.Normal :=
    ⟨fun x hx g => (hA _).2 (hr pt g x (Subgroup.mem_top _) ((hA x).1 hx))⟩
  have : Group.IsSolvable A := Group.isSolvable_of_surjective φr.rangeRestrict_surjective
  have : Group.IsSolvable B := Group.isSolvable_of_surjective φn.rangeRestrict_surjective
  have : Group.IsSolvable ↥(A ⊔ B) := isSolvable_sup_of_normal A B
  have hφ : ∀ x, φ x ∈ A ⊔ B := by
    intro x
    obtain ⟨a, b, ha, hb, he⟩ := hp.exists_mul_of_rationalPoint (x := φ x) ⟨x, rfl⟩
    rw [he]
    exact Subgroup.mul_mem_sup ((hA a).2 ha) ((hB b).2 hb)
  have : Mono p.hom.hom := by
    have : Mono p.hom.hom.left := hp.isClosedSubgroup.mono
    exact Over.mono_of_mono_left _
  have hinj : Function.Injective (φ.codRestrict (A ⊔ B) hφ) := fun x y hxy =>
    (inferInstance : Mono p.hom.hom).right_cancellation x y (congrArg Subtype.val hxy)
  exact Group.isSolvable_of_isSolvable_injective hinj

/-! ### The radical torus intersection -/

/-- **Radical torus intersections, conditional on the solvable torus quotient.** The
existence of the split torus quotient of a smooth connected solvable group with unipotent kernel
(`SolvableTorusQuotientStatement`, Milne 2017, Theorem 16.33(a), (c)) gives the maximal-rank
radical intersection statement. The maximal torus `f : T → H` normalizes the radical `r`, so
`P = R · T` is a smooth connected solvable closed subgroup of `H` containing both; its maximal
tori are conjugate (`maximalToriAreConjugate_of_solvableTorusQuotient`), and the intersection is
computed in `P` by `exists_radicalTorusIntersection_of_complement`. -/
theorem maximalRankRadicalTorusIntersectionStatement_of_solvableTorusQuotient
    (hquot : SolvableTorusQuotientStatement.{u}) :
    MaximalRankRadicalTorusIntersectionStatement.{u} := by
  intro k _ _ G hG H j hj hHs hHc T t ht f hft R r hR
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffineHom H.X.hom := hj.isAffineHom
  have : Smooth H.X.hom := hHs
  have : Smooth R.X.hom := hR.smooth
  have : ConnectedSpace R.X.left := hR.connectedSpace
  have : IsAffineHom R.X.hom := hR.isClosedSubgroup.isAffineHom
  have hf : IsMaximalTorus f := IsMaximalTorus.of_comp hj (hft ▸ ht)
  have : Smooth T.toGrp.X.hom := hf.1.smooth
  have : ConnectedSpace T.toGrp.X.left := hf.1.connectedSpace
  have hfc : IsClosedSubgroup f := hf.2.1
  have hnr : (SubgroupFunctor.range r).IsNormalizedBy (SubgroupFunctor.range f) :=
    fun V g x _ hx => hR.isNormal V g x (Subgroup.mem_top _) hx
  -- The product `P = R · T` and its inclusion `p`.
  let P := SubgroupFunctor.smoothConnectedProduct r f hR.isClosedSubgroup hfc hnr
  let p := SubgroupFunctor.smoothConnectedProductι r f hR.isClosedSubgroup hfc hnr
  obtain ⟨hprod, hPs, hPc⟩ :=
    SubgroupFunctor.smoothConnectedProductι_spec r f hR.isClosedSubgroup hfc hnr
  have hp : IsClosedSubgroup p := hprod.isClosedSubgroup
  have : IsClosedImmersion p.hom.hom.left := hp
  have hpm : Mono p.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom P.X.hom := hp.isAffineHom
  have : Smooth P.X.hom := hPs
  have : ConnectedSpace P.X.left := hPc
  -- `R` and `T` factor through `P`.
  have hrep := hp.isRepresentedBy_range
  let r' := hrep.factorHom r hprod.left_le
  let f' := hrep.factorHom f hprod.right_le
  have hr' : r' ≫ p = r := hrep.factorHom_comp r _
  have hf' : f' ≫ p = f := hrep.factorHom_comp f _
  have hf'max : IsMaximalTorus f' := IsMaximalTorus.of_comp hp (by rw [hf']; exact hf)
  have hr'cl : IsClosedSubgroup r' :=
    IsClosedSubgroup.of_comp hp (by rw [hr']; exact hR.isClosedSubgroup)
  have hn' : (SubgroupFunctor.range r').IsNormal := by
    intro V g x _ hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    let φ := IsMonHom.monoidHom p.hom.hom V
    have hmem : φ (g * (y ≫ r'.hom.hom) * g⁻¹) ∈ (SubgroupFunctor.range r).carrier V := by
      rw [map_mul, map_mul, map_inv]
      refine hR.isNormal V (φ g) (φ (y ≫ r'.hom.hom)) (Subgroup.mem_top _) ⟨y, ?_⟩
      change y ≫ r.hom.hom = (y ≫ r'.hom.hom) ≫ p.hom.hom
      rw [Category.assoc, ← Grp.comp_hom_hom, hr']
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.1 hmem
    refine SubgroupFunctor.mem_range.2 ⟨z, hpm.right_cancellation _ _ ?_⟩
    change (z ≫ r'.hom.hom) ≫ p.hom.hom = (g * (y ≫ r'.hom.hom) * g⁻¹) ≫ p.hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, hr']
    exact hz
  -- `P` is solvable, so its maximal tori are conjugate.
  have hPsolv : IsSolvableGroupScheme P :=
    hprod.isSolvableGroupScheme hR.isNormal hR.isSolvableGroupScheme
      (CommGroupScheme.isSolvableGroupScheme T)
  have hsec := solvableSplitExtension_of_oneDimensional perfectFieldOneDimensionalUnipotent
  have hconjP := maximalToriAreConjugate_of_solvableTorusQuotient hquot hsec k P hPsolv
  obtain ⟨S, sT, sR, hsT, hsR, hsq, hrange⟩ :=
    exists_radicalTorusIntersection_of_complement unipotentClosedSubgroup hconjP f' hf'max
      (IsTorus.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting hf.1) r' hr'cl
      hn' (fun S s hs => by
        obtain ⟨U, u, hu, -, -, hU, -, -, hiso⟩ :=
          solvableMaximalTorusSemidirectStatement_of_solvableTorusQuotient hquot hsec k R
            hR.isSolvableGroupScheme S s hs
        exact ⟨U, u, hu, hU, hiso⟩)
  have hsq' : sT ≫ f = sR ≫ r := calc
    sT ≫ f = sT ≫ f' ≫ p := by rw [hf']
    _ = sR ≫ r' ≫ p := by rw [← Category.assoc, hsq, Category.assoc]
    _ = sR ≫ r := by rw [hr']
  refine ⟨S, sT, sR, hsT, hsR, hsq', ?_⟩
  -- Transport the intersection from `P` to `H` along the monomorphism `p`.
  apply le_antisymm
  · intro V x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    refine ⟨SubgroupFunctor.mem_range.2 ⟨y ≫ sT.hom.hom, ?_⟩,
      SubgroupFunctor.mem_range.2 ⟨y ≫ sR.hom.hom, ?_⟩⟩
    · change (y ≫ sT.hom.hom) ≫ f.hom.hom = y ≫ (sT ≫ f).hom.hom
      rw [Grp.comp_hom_hom, Category.assoc]
    · change (y ≫ sR.hom.hom) ≫ r.hom.hom = y ≫ (sT ≫ f).hom.hom
      rw [hsq', Grp.comp_hom_hom, Category.assoc]
  · rintro V x ⟨hxf, hxr⟩
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 hxf
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.1 hxr
    have hyz : y ≫ f'.hom.hom = z ≫ r'.hom.hom := by
      apply hpm.right_cancellation
      rw [Category.assoc, Category.assoc, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, hf', hr',
        hy, hz]
    have hmem : y ≫ f'.hom.hom ∈ (SubgroupFunctor.range (sT ≫ f')).carrier V := by
      rw [hrange]
      exact ⟨SubgroupFunctor.mem_range.2 ⟨y, rfl⟩, SubgroupFunctor.mem_range.2 ⟨z, hyz.symm⟩⟩
    obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.1 hmem
    refine SubgroupFunctor.mem_range.2 ⟨w, ?_⟩
    calc w ≫ (sT ≫ f).hom.hom = w ≫ (sT ≫ f' ≫ p).hom.hom := by rw [hf']
      _ = (w ≫ (sT ≫ f').hom.hom) ≫ p.hom.hom := by
          simp only [Grp.comp_hom_hom, Category.assoc]
      _ = (y ≫ f'.hom.hom) ≫ p.hom.hom := by rw [hw]
      _ = x := by rw [Category.assoc, ← Grp.comp_hom_hom, hf', hy]

end AlgebraicallyClosed

end Langlands.GroupScheme
