import Langlands.GroupScheme.Reductive.CorootCommutator
import Langlands.GroupScheme.Reductive.EtaleCorootNormalizer

/-! # Coroot points are fppf-locally commutators -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeDerived

variable {S : Scheme.{u}} {G : GroupScheme S} {D : CommGroupScheme S}

/-- The all-test transporter relation also gives the inversion commutator
identity for a normalizing point on an arbitrary test scheme. -/
theorem mem_commutator_of_inverted_transporter_square
    (i : D.toGrp ⟶ G) (h : cocharacterLattice D) (σ : D ≅ D)
    (hinv : h ≫ σ.hom = -h) {Z : Over S} (m : Z ⟶ G.X)
    (hm : PointwiseSchemeAction.IsTransporter (CommGroupScheme.groupHom σ.hom ≫ i) i m)
    (z : Z ⟶ (Gm S).X) :
    (z ≫ (CommGroupScheme.groupHom h).hom.hom ≫ i.hom.hom) ^ 2 ∈
      _root_.commutator (Z ⟶ G.X) := by
  apply square_mem_commutator_of_conj_inv m
  have he := hm Z (𝟙 Z) (z ≫ (CommGroupScheme.groupHom h).hom.hom)
  simp only [Category.id_comp, Grp.comp_hom_hom] at he
  have hh : (z ≫ (CommGroupScheme.groupHom h).hom.hom) ≫
      (CommGroupScheme.groupHom σ.hom).hom.hom ≫ i.hom.hom =
      (z ≫ (CommGroupScheme.groupHom h).hom.hom ≫ i.hom.hom)⁻¹ := by
    calc
      _ = z ≫ (CommGroupScheme.groupHom (h ≫ σ.hom)).hom.hom ≫ i.hom.hom := by
        change (z ≫ (CommGroupScheme.groupHom h).hom.hom) ≫
          (CommGroupScheme.groupHom σ.hom).hom.hom ≫ i.hom.hom =
          z ≫ ((CommGroupScheme.groupHom h).hom.hom ≫
            (CommGroupScheme.groupHom σ.hom).hom.hom) ≫ i.hom.hom
        simp only [Category.assoc]
      _ = _ := by
        rw [hinv]
        change z ≫ ((CommGroupScheme.groupHom h).hom.hom)⁻¹ ≫ i.hom.hom = _
        rw [← Category.assoc z, GrpObj.comp_inv, GrpObj.inv_comp, Category.assoc]
  rw [hh] at he
  simp only [Category.assoc] at he
  rw [← he, mul_inv_cancel_right]

/-- A transporter inverting a cocharacter makes every parameter point over
an affine test scheme fppf-locally a commutator. -/
theorem locallyCommutator_of_inverted_transporter_affine
    (i : D.toGrp ⟶ G) (h : cocharacterLattice D) (σ : D ≅ D)
    (hinv : h ≫ σ.hom = -h) {Z : Over S} [IsAffine Z.left] (m : Z ⟶ G.X)
    (hm : PointwiseSchemeAction.IsTransporter (CommGroupScheme.groupHom σ.hom ≫ i) i m)
    (t : Z ⟶ (Gm S).X) :
    LocallyCommutator (t ≫ (CommGroupScheme.groupHom h).hom.hom ≫ i.hom.hom) := by
  obtain ⟨W, j, hW, hflat, hsurj, hfp, r, hr⟩ :=
    UnitPowerExtension.exists_roots_test Z 2 (by decide)
      (fun _ : Fin 1 => Gm.pointsEquiv S Z t)
  let : Flat j.left := hflat
  let : Surjective j.left := hsurj
  let : LocallyOfFinitePresentation j.left := hfp
  let z : W ⟶ (Gm S).X := (Gm.pointsEquiv S W).symm (r 0)
  have hz : z ^ 2 = j ≫ t := by
    apply (Gm.pointsEquiv S W).injective
    rw [map_pow, MulEquiv.apply_symm_apply, Gm.pointsEquiv_naturality]
    exact hr 0
  apply LocallyCommutator.of_surjective j
  apply LocallyCommutator.of_mem
  have hm := mem_commutator_of_inverted_transporter_square i h σ hinv (j ≫ m) (hm.restrict j) z
  have he : (z ≫ (CommGroupScheme.groupHom h).hom.hom ≫ i.hom.hom) ^ 2 =
      j ≫ (t ≫ (CommGroupScheme.groupHom h).hom.hom ≫ i.hom.hom) := by
    rw [← MonObj.pow_comp, hz]
    simp only [Category.assoc]
  rw [he] at hm
  exact hm

/-- The same transporter criterion holds on arbitrary test schemes. -/
theorem locallyCommutator_of_inverted_transporter
    (i : D.toGrp ⟶ G) (h : cocharacterLattice D) (σ : D ≅ D)
    (hinv : h ≫ σ.hom = -h) {Z : Over S} (m : Z ⟶ G.X)
    (hm : PointwiseSchemeAction.IsTransporter (CommGroupScheme.groupHom σ.hom ≫ i) i m)
    (t : Z ⟶ (Gm S).X) :
    LocallyCommutator (t ≫ (CommGroupScheme.groupHom h).hom.hom ≫ i.hom.hom) := by
  let 𝒰 : Scheme.Cover.{u}
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) Z.left :=
    Z.left.affineCover.changeProp (fun j => by
      have := Z.left.affineCover.map_prop j
      exact ⟨inferInstance, inferInstance⟩)
  apply LocallyCommutator.of_cover 𝒰
  intro j
  let U : Over S := Over.mk (𝒰.f j ≫ Z.hom)
  let a : U ⟶ Z := Over.homMk (𝒰.f j) rfl
  have : IsAffine U.left := inferInstanceAs (IsAffine (Z.left.affineCover.X j))
  exact locallyCommutator_of_inverted_transporter_affine i h σ hinv
    (a ≫ m) (hm.restrict a) (a ≫ t)

end Langlands.GroupScheme.RelativeDerived

namespace Langlands.GroupScheme.RelativeDerived

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- Every point of every coordinate coroot of a fibrewise root datum is
fppf-locally in the abstract commutator subgroup. -/
theorem locallyCommutator_coroot (hG : IsReductive G)
    (hP : IsFibrewiseRootDatumOf I G i P) (a : J)
    (Z : Over (Spec (CommRingCat.of R))) (t : Z ⟶ (Gm (Spec (CommRingCat.of R))).X) :
    LocallyCommutator
      (t ≫ (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I (P.coroot a))).hom.hom ≫
          i.hom.hom) := by
  classical
  choose U f hU hf hs n hn using fun s => exists_etale_coordinateReflection hG hP s a
  let 𝒱 : Scheme.Cover.{u} (Scheme.precoverage @Etale) (Spec (CommRingCat.of R)) :=
    Scheme.Cover.mkOfCovers (Spec (CommRingCat.of R)) U f
      (fun s => by obtain ⟨v, hv⟩ := hs s; exact ⟨s, v, hv⟩) hf
  let 𝒰 : Scheme.Cover.{u}
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) Z.left :=
    Scheme.Cover.changeProp (𝒱.pullback₁ Z.hom) (fun j => by
      have := Scheme.Cover.map_prop (𝒱.pullback₁ Z.hom) j
      exact ⟨inferInstance, inferInstance⟩)
  apply LocallyCommutator.of_cover 𝒰
  intro s
  let b := f s
  let W : Over (Spec (CommRingCat.of R)) :=
    Over.mk (pullback.fst Z.hom b ≫ Z.hom)
  let q : W ⟶ (Over.map b).obj (Over.mk (𝟙 (U s))) :=
    Over.homMk (pullback.snd Z.hom b) (by
      change pullback.snd Z.hom b ≫ ((𝟙 (U s)) ≫ b) =
        pullback.fst Z.hom b ≫ Z.hom
      simpa only [Category.id_comp] using (pullback.condition (f := Z.hom) (g := b)).symm)
  let σ := (splitTorus.exponentCommIso (Spec (CommRingCat.of R)) I (P.reflection a)).symm
  have ht : PointwiseSchemeAction.IsTransporter
      ((GroupScheme.baseChange b).map (CommGroupScheme.groupHom σ.hom ≫ i))
      ((GroupScheme.baseChange b).map i) (n s) := by
    rw [Functor.map_comp]
    exact (hn s).isTransporter
  have hm := ht.baseChangePointsEquiv b
  let k := (Spec (CommRingCat.of R)).residueField s
  let : Algebra R k :=
    (Spec.preimage ((Spec (CommRingCat.of R)).fromSpecResidueField s)).hom.toAlgebra
  have hinv := splitTorus.exponentCocharacter_comp_reflection
    (Spec (CommRingCat.of R)) P (hP.pairing k) a
  let e : W ⟶ Z := Over.homMk (pullback.fst Z.hom b) rfl
  exact locallyCommutator_of_inverted_transporter i
    (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I (P.coroot a)) σ hinv
    (q ≫ baseChangePointsEquiv b G (Over.mk (𝟙 (U s))) (n s)) (hm.restrict q) (e ≫ t)

end Langlands.GroupScheme.RelativeDerived

namespace Langlands.GroupScheme.RelativeDerived

/-- A chosen actual fppf cover witnessing commutator membership of a coroot point. -/
def corootCommutatorCover
    {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hG : IsReductive G) (hP : IsFibrewiseRootDatumOf I G i P) (a : J)
    (Z : Over (Spec (CommRingCat.of R))) (t : Z ⟶ (Gm (Spec (CommRingCat.of R))).X) :
    Scheme.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) Z.left :=
  (locallyCommutator_coroot hG hP a Z t).choose

/-- Each member of the chosen coroot cover gives abstract commutator membership. -/
theorem corootCommutatorCover_mem
    {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hG : IsReductive G) (hP : IsFibrewiseRootDatumOf I G i P) (a : J)
    (Z : Over (Spec (CommRingCat.of R))) (t : Z ⟶ (Gm (Spec (CommRingCat.of R))).X)
    (j : (corootCommutatorCover hG hP a Z t).I₀) :
    (Over.homMk ((corootCommutatorCover hG hP a Z t).f j) rfl :
      Over.mk ((corootCommutatorCover hG hP a Z t).f j ≫ Z.hom) ⟶ Z) ≫
      (t ≫ (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I (P.coroot a))).hom.hom ≫
          i.hom.hom) ∈ _root_.commutator _ :=
  (locallyCommutator_coroot hG hP a Z t).choose_spec j

end Langlands.GroupScheme.RelativeDerived
