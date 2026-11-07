import Langlands.GroupScheme.Rational.RankOneParabolicTorusConjugacy
import Langlands.GroupScheme.FixedCosetFactorization

/-! # Rational normalizer representatives for descended rank-one fixed cosets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (a : characterLattice T) (ha : a ≠ 0)
    (e : AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp G)
    (he : e.restrict (CommGroupScheme.groupHom a) = AutomorphicAction.conjugation i)
    (ν : cocharacterLattice T) (hpos : 0 < latticePairing T a ν)

include hi ha he hpos

/-- A rational conjugate of the maximal split torus contained in the dynamic
parabolic can be adjusted by an actual rational unipotent point to normalize it. -/
theorem exists_unipotent_normalizer_adjustment_of_range_le
    [Smooth G.X.hom]
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hg : SubgroupFunctor.range (i ≫ (G.innerIso g⁻¹).hom) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)) :
    ∃ u : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      u ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier
        (Over.mk (𝟙 _)) ∧ g * u ∈ normalizerPoints i := by
  obtain ⟨u, hu, f, hfiso, hf⟩ :=
    exists_unipotent_conjugacy_of_range_le_parabolic_descendedAction
      i hi a ha e he ν hpos (i ≫ (G.innerIso g⁻¹).hom)
      (hi.comp_iso (G.innerIso g⁻¹)) hg
  let : IsIso f := hfiso
  let σ : T ≅ T :=
    { hom := Additive.ofMul (inv f)
      inv := Additive.ofMul f
      hom_inv_id := congrArg Additive.ofMul (IsIso.inv_hom_id f)
      inv_hom_id := congrArg Additive.ofMul (IsIso.hom_inv_id f) }
  refine ⟨u, hu, σ, ?_⟩
  change i ≫ (G.innerIso (g * u)).hom = inv f ≫ i
  apply (cancel_epi f).mp
  rw [IsIso.hom_inv_id_assoc]
  rw [innerIso_mul_hom, ← Category.assoc f i, ← Category.assoc, hf,
    innerIso_inv_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    (hfib : ∀ (V : Over (Spec (CommRingCat.of k))) (x y : V ⟶ G.X),
      x ≫ q = y ≫ q ↔ x⁻¹ * y ∈
        (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier V)

include hfib

omit [IsAffineHom G.X.hom] hi ha in
/-- A quotient coset fixed by the positively pairing cocharacter is fixed by
the whole split torus, on every test scheme. -/
theorem torus_fixed_coset_of_cocharacter_fixed
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hfixed : ∀ (V : Over (Spec (CommRingCat.of k)))
      (z : V ⟶ (Gm (Spec (CommRingCat.of k))).X),
      ((z ≫ (CommGroupScheme.groupHom ν ≫ i).hom.hom) *
        G.constantPoint g V) ≫ q = G.constantPoint g V ≫ q) :
    ∀ (V : Over (Spec (CommRingCat.of k))) (t : V ⟶ T.toGrp.X),
      ((t ≫ i.hom.hom) * G.constantPoint g V) ≫ q =
        G.constantPoint g V ≫ q := by
  let N := latticePairing T a ν
  let p := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) N)
  have hp0 : Gm.powerHom (Spec (CommRingCat.of k)) N ≠ 0 := by
    intro h
    exact (ne_of_gt hpos) ((Gm.powerHom_injective k) (h.trans (map_zero _).symm))
  obtain ⟨hpqc, hpflat, hpsurj⟩ := characterFpqc k (Gm (Spec (CommRingCat.of k)))
    isSplitTorus_gm (Gm.powerHom _ N) hp0
  let : QuasiCompact p.hom.hom.left := hpqc
  let : Flat p.hom.hom.left := hpflat
  let : Surjective p.hom.hom.left := hpsurj
  have hνa : CommGroupScheme.groupHom ν ≫ CommGroupScheme.groupHom a = p := by
    change CommGroupScheme.groupHom (ν ≫ a) = _
    congr 1
    exact eq_gmEndEquiv_zsmul k (ν ≫ a)
  have hright (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ G.X)
      (t : V ⟶ T.toGrp.X) : (x * (t ≫ i.hom.hom)) ≫ q = x ≫ q := by
    apply Eq.symm
    apply (hfib V _ _).mpr
    rw [inv_mul_cancel_left]
    exact ((range_le_torusCentralizer i).trans
      ((torusCentralizer_le_dynamicCentralizer i (CommGroupScheme.groupHom ν)).trans
        (Dynamic.centralizer_le_parabolic _))) V
      (SubgroupFunctor.mem_range.mpr ⟨t, rfl⟩)
  have hconjq (V : Over (Spec (CommRingCat.of k))) (t : V ⟶ T.toGrp.X)
      (x : V ⟶ G.X) :
      e.act (t ≫ (CommGroupScheme.groupHom a).hom.hom) x ≫ q =
        ((t ≫ i.hom.hom) * x) ≫ q := by
    have hc := congrArg (fun d : AutomorphicAction T.toGrp G => d.act t x) he
    simp only [AutomorphicAction.restrict_act, AutomorphicAction.conjugation_act] at hc
    rw [hc]
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using
      (hright V ((t ≫ i.hom.hom) * x * (t ≫ i.hom.hom)⁻¹) t).symm
  have hpe (V : Over (Spec (CommRingCat.of k)))
      (z : V ⟶ (Gm (Spec (CommRingCat.of k))).X) :
      e.act (z ≫ p.hom.hom) (G.constantPoint g V) ≫ q =
        G.constantPoint g V ≫ q := by
    rw [← hνa, Grp.comp_hom_hom, ← Category.assoc, hconjq]
    simpa only [Grp.comp_hom_hom, Category.assoc] using hfixed V z
  intro V t
  calc
    ((t ≫ i.hom.hom) * G.constantPoint g V) ≫ q =
        e.act (t ≫ (CommGroupScheme.groupHom a).hom.hom)
          (G.constantPoint g V) ≫ q := (hconjq V t _).symm
    _ = G.constantPoint g V ≫ q := by
      apply AutomorphicAction.hom_ext_of_local_quotient_lift p
        (t ≫ (CommGroupScheme.groupHom a).hom.hom)
      intro W d z hdz
      rw [← Category.assoc, ← Category.assoc, e.naturality,
        G.constantPoint_naturality, hdz]
      exact hpe W z

/-- The actual normalizer representative obtained by adjusting a fixed coset
inside its dynamic unipotent subgroup. -/
def normalizerRepresentativeOfFixedCoset [Smooth G.X.hom]
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hfixed : ∀ (V : Over (Spec (CommRingCat.of k)))
      (z : V ⟶ (Gm (Spec (CommRingCat.of k))).X),
      ((z ≫ (CommGroupScheme.groupHom ν ≫ i).hom.hom) *
        G.constantPoint g V) ≫ q = G.constantPoint g V ≫ q) :
    {n : normalizerPoints i // n.val ≫ q = g ≫ q ∧
      g⁻¹ * n.val ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier
        (Over.mk (𝟙 _))} := by
  have hTfixed := torus_fixed_coset_of_cocharacter_fixed i a e he ν hpos
    q hfib g hfixed
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let j := Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom ν ≫ i)
  have hj := Dynamic.Affine.isRepresentedBy_parabolicHom (CommGroupScheme.groupHom ν ≫ i)
  have hfib' : ∀ (V : Over (Spec (CommRingCat.of k))) (x y : V ⟶ G.X),
      x ≫ q = y ≫ q ↔ x⁻¹ * y ∈ (SubgroupFunctor.range j).carrier V := by
    intro V x y
    change _ ↔ _ ∈ (SubgroupFunctor.range
      (Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom ν ≫ i))).carrier V
    rw [hj.2]
    exact hfib V x y
  have hg : SubgroupFunctor.range (i ≫ (G.innerIso g⁻¹).hom) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) := by
    rw [← hj.2]
    exact range_conjugate_le_of_fixed_coset i j q hfib' g hTfixed
  let hex := exists_unipotent_normalizer_adjustment_of_range_le
    i hi a ha e he ν hpos g hg
  let u := Classical.choose hex
  have hu := (Classical.choose_spec hex).1
  have hn := (Classical.choose_spec hex).2
  refine ⟨⟨g * u, hn⟩, ?_, ?_⟩
  · apply Eq.symm
    apply (hfib _ _ _).mpr
    rw [inv_mul_cancel_left]
    exact Dynamic.unipotent_le_parabolic _ _ hu
  · simpa only [inv_mul_cancel_left] using hu

end Langlands.GroupScheme.RelativeRoot
