import Langlands.GroupScheme.Rational.FiniteFieldMaximalTorusTransporterStatement
import Langlands.GroupScheme.Rational.FiniteFieldCentralCocharacterEnvelopeNormalityStatement
import Langlands.GroupScheme.Rational.FiniteFieldDynamicUnipotentEnvelope
import Langlands.GroupScheme.Rational.DynamicCellTransporter
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.Rational.MaximalSplitTorusCentralizer
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Torus.Products
import Langlands.GroupScheme.Dynamic.LeviCocharacterCombination

/-! # Reduction of the finite-field maximal-torus transporter to the central-cocharacter case -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- The closed torus envelope of a closed subgroup maps into the closed torus envelope of the
ambient group, on every test scheme. -/
theorem closedTorusEnvelope_comp_mem {Z G : GroupScheme (Spec (CommRingCat.of k))}
    {iZ : Z ⟶ G} (hiZ : IsClosedSubgroup iZ) {U : Over (Spec (CommRingCat.of k))}
    {y : U ⟶ Z.X} (hy : y ∈ (closedTorusEnvelope Z).carrier U) :
    y ≫ iZ.hom.hom ∈ (closedTorusEnvelope G).carrier U := by
  intro H' j' hj' ht
  have hpbO := IsPullback.map (Grp.forget (Over (Spec (CommRingCat.of k))))
    (IsPullback.of_hasPullback j' iZ)
  change IsPullback (pullback.fst j' iZ).hom.hom (pullback.snd j' iZ).hom.hom
    j'.hom.hom iZ.hom.hom at hpbO
  have hpbS := hpbO.map (Over.forget (Spec (CommRingCat.of k)))
  have : IsClosedImmersion j'.hom.hom.left := hj'
  have hsnd : IsClosedSubgroup (pullback.snd j' iZ) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpbS this
  have hrange : (SubgroupFunctor.range (pullback.snd j' iZ)).ContainsTori := by
    intro T i hT hi V x hx
    obtain ⟨t, rfl⟩ := hx
    have hm : (t ≫ i.hom.hom) ≫ iZ.hom.hom ∈ (SubgroupFunctor.range j').carrier V :=
      ht T (i ≫ iZ) hT (hi.comp hiZ) V ⟨t, by
        change t ≫ (i ≫ iZ).hom.hom = _
        rw [Grp.comp_hom_hom, Category.assoc]⟩
    obtain ⟨h, hh⟩ := hm
    change h ≫ j'.hom.hom = (t ≫ i.hom.hom) ≫ iZ.hom.hom at hh
    exact ⟨hpbO.lift h (t ≫ i.hom.hom) hh, hpbO.lift_snd _ _ _⟩
  obtain ⟨p, hp⟩ := closedTorusEnvelope_le _ hsnd hrange U hy
  change p ≫ (pullback.snd j' iZ).hom.hom = y at hp
  refine ⟨p ≫ (pullback.fst j' iZ).hom.hom, ?_⟩
  change (p ≫ (pullback.fst j' iZ).hom.hom) ≫ j'.hom.hom = y ≫ iZ.hom.hom
  rw [Category.assoc, hpbO.w, ← Category.assoc, hp]

/-- A central homomorphism from a torus into a smooth affine group factors through every
maximal torus. -/
theorem IsCentral.exists_factor_of_isMaximalTorus {M A : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth M.X.hom] [IsAffineHom M.X.hom] (hA : IsTorus A) {a : A ⟶ M} (ha : IsCentral a)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {t : T.toGrp ⟶ M} (ht : IsMaximalTorus t) :
    ∃ g : A ⟶ T.toGrp, g ≫ t = a := by
  let hab := ha.commute_values t
  obtain ⟨Z, j, f, hZ, hj, hf⟩ :=
    torusImageClosedTorusStatement k M (A ⊗ T.toGrp) (hA.tensor ht.1) (prodHom a t hab)
  have he : (prodInr A T.toGrp ≫ f) ≫ j = t := by
    rw [Category.assoc, hf, prodInr_prodHom]
  have hiso : IsIso (prodInr A T.toGrp ≫ f) := ht.2.2 Z j _ hZ hj he
  refine ⟨(prodInl A T.toGrp ≫ f) ≫ inv (prodInr A T.toGrp ≫ f), ?_⟩
  rw [← he, Category.assoc, IsIso.inv_hom_id_assoc, Category.assoc, hf, prodInl_prodHom]

/-- The finite-field central-cocharacter case of envelope normality implies the finite-field
maximal-torus transporter statement: induction on the Lie dimension through dynamic
centralizers of noncentral cocharacters. -/
theorem finiteFieldMaximalTorusTransporter_of
    (hbase : FiniteFieldCentralCocharacterEnvelopeNormalityStatement.{u}) :
    FiniteFieldMaximalTorusTransporterStatement.{u} := by
  intro k _ _ G _ _ _
  refine smoothConnectedAffineGroup_lieDimension_induction (k := k)
    (fun G => ∃ (T₀ : CommGroupScheme (Spec (CommRingCat.of k))) (j₀ : T₀.toGrp ⟶ G),
      IsMaximalTorus j₀ ∧ ∀ (U : Over (Spec (CommRingCat.of k))) (g x : U ⟶ G.X),
        x ∈ (SubgroupFunctor.range j₀).carrier U →
          g * x * g⁻¹ ∈ (closedTorusEnvelope G).carrier U) ?_ G
  intro G _ _ _ ih
  by_cases hc : ∀ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G, Dynamic.centralizer χ = ⊤
  · obtain ⟨T₀, j₀, hj₀⟩ := TorusExistence.exists_isMaximalTorus (G := G)
    refine ⟨T₀, j₀, hj₀, fun U g x hx => ?_⟩
    exact hbase k G hc U g x (Subgroup.mem_top g)
      (closedTorusEnvelope_containsTori G T₀ j₀ hj₀.1 hj₀.2.1 U hx)
  push Not at hc
  obtain ⟨χ, hχ⟩ := hc
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let Z := Dynamic.Affine.centralizerScheme χ
  let iZ := Dynamic.Affine.centralizerHom χ
  have hZrep := Dynamic.Affine.isRepresentedBy_centralizerHom χ
  have hZc := Dynamic.Affine.isClosedSubgroup_centralizerHom χ
  have : IsAffineHom Z.X.hom := hZc.isAffineHom
  have : Smooth Z.X.hom := (dynamicSmooth k G χ Z iZ).2.1 hZrep
  have : ConnectedSpace Z.X.left := ((dynamicConnected k G χ Z iZ).2 inferInstance).2 hZrep
  have hnotiso : ¬ IsIso iZ := by
    intro h
    apply hχ
    rw [← hZrep.2]
    refine SubgroupFunctor.ext fun U => Subgroup.ext fun g => ⟨fun _ => Subgroup.mem_top g,
      fun _ => ?_⟩
    exact ⟨g ≫ (inv iZ).hom.hom, by
      change (g ≫ (inv iZ).hom.hom) ≫ iZ.hom.hom = g
      rw [Category.assoc, ← Grp.comp_hom_hom, IsIso.inv_hom_id, Grp.id_hom_hom,
        Category.comp_id]⟩
  obtain ⟨T₀, j₀', hj₀', htr'⟩ := ih Z (Lie.dimension_lt_of_proper_closedSubgroup iZ hZc hnotiso)
  have hχZ : SubgroupFunctor.range χ ≤ Dynamic.centralizer χ := by
    rw [← torusCentralizer_gm_eq_dynamicCentralizer]
    exact range_le_torusCentralizer χ
  let χ' := hZrep.factorHom χ hχZ
  have hχ' : χ' ≫ iZ = χ := hZrep.factorHom_comp χ hχZ
  have hZmono : Mono iZ.hom.hom := hZrep.1
  have hcent : IsCentral χ' := by
    intro T x T' a h
    apply hZmono.right_cancellation
    rw [MonObj.mul_comp, MonObj.mul_comp]
    have hh : h ≫ iZ.hom.hom ∈ (Dynamic.centralizer χ).carrier T' := by
      rw [← hZrep.2]
      exact ⟨h, rfl⟩
    have hcomm := Dynamic.commute_cocharacter_of_mem_centralizer χ hh (a ≫ x)
    have hx : (a ≫ x ≫ χ'.hom.hom) ≫ iZ.hom.hom = (a ≫ x) ≫ χ.hom.hom := by
      have h := congrArg (fun f : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G =>
        (a ≫ x) ≫ f.hom.hom) hχ'
      simp only [Grp.comp_hom_hom, Category.assoc] at h ⊢
      exact h
    rw [hx]
    exact hcomm.eq.symm
  obtain ⟨ψ, hψ⟩ := IsCentral.exists_factor_of_isMaximalTorus
    (isSplitTorus_gm (S := Spec (CommRingCat.of k))).isTorus hcent hj₀'
  have hj₀ : IsMaximalTorus (j₀' ≫ iZ) := by
    refine ⟨hj₀'.1, hj₀'.2.1.comp hZc, fun T'' i'' f hT'' hi'' hf => ?_⟩
    have hfac : (ψ ≫ f) ≫ i'' = χ := by
      rw [Category.assoc, hf, ← Category.assoc, hψ, hχ']
    have hrange : SubgroupFunctor.range i'' ≤ Dynamic.centralizer χ := by
      rw [← torusCentralizer_gm_eq_dynamicCentralizer]
      exact range_le_torusCentralizer_of_factor (A := Gm (Spec (CommRingCat.of k))) χ i''
        (ψ ≫ f) hfac
    let i''' := hZrep.factorHom i'' hrange
    have hi''' : i''' ≫ iZ = i'' := hZrep.factorHom_comp i'' hrange
    have hi'''c : IsClosedSubgroup i''' := IsClosedSubgroup.of_comp hZc (by rw [hi''']; exact hi'')
    exact hj₀'.2.2 T'' i''' f hT'' hi'''c (hZrep.hom_ext (by rw [Category.assoc, hi''', hf]))
  refine ⟨T₀, j₀' ≫ iZ, hj₀, ?_⟩
  let D := smoothTorusGeneratedEnvelope G
  have hU := unipotent_le_closedTorusEnvelope G χ
  have hU' := unipotent_le_closedTorusEnvelope G
    (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)
  have : Smooth T₀.toGrp.X.hom := hj₀'.1.smooth
  intro U g x hx
  refine Dynamic.conj_mem_of_centralizer_conj_mem χ D.represents D.closed hU hU' (j₀' ≫ iZ)
    (fun T z y hz hy => ?_) U g x hx
  rw [← hZrep.2] at hz
  obtain ⟨z', rfl⟩ := hz
  obtain ⟨t, rfl⟩ := hy
  have h1 := htr' T z' (t ≫ j₀'.hom.hom) ⟨t, rfl⟩
  have h2 := closedTorusEnvelope_comp_mem hZc h1
  change z' ≫ iZ.hom.hom * (t ≫ (j₀' ≫ iZ).hom.hom) * (z' ≫ iZ.hom.hom)⁻¹ ∈ _
  simpa only [MonObj.mul_comp, GrpObj.inv_comp, Grp.comp_hom_hom, Category.assoc] using h2

end Langlands.GroupScheme
