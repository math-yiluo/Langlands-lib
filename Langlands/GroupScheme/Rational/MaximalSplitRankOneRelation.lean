import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.RootFactorPairConsequences
import Langlands.GroupScheme.Rational.RootSubgroupConjugation
import Langlands.GroupScheme.Rational.CharacterFpqcProof
import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Reductive.SplitRankOneRootCellUniversal
import Langlands.GroupScheme.Reductive.LocalWeylNormalizationField
import Langlands.GroupScheme.Reductive.LocalSplitFieldComparison
import Langlands.GroupScheme.Reductive.RankOneRootCellRelation
import Langlands.GroupScheme.Reductive.PinningLattice
import Langlands.GroupScheme.CentralIsogeny.CorootCompatibility
import Langlands.GroupScheme.MatrixRepresentation.TorusEquivariantAdditive

/-! # The rank-one relation for an equivariant line in a nonmultipliable root group

Let `i : S ⟶ G` be a maximal split torus of a connected reductive group over a field `k`,
`a` a relative root with `2a` not a root, and `x : 𝔾ₐ ⟶ G` a monic `a`-equivariant line in
the root group `U_(a)`. The rank-one factorization of `u = x(1)` gives `n = v u v` normalizing
the torus, with `v = n⁻¹ u n`. Put `y(t) = n⁻¹ x(-t) n`, so that `v = y(-1)`. The coroot `ν`
of the factor pair makes `n` act on the torus by `s_a = 1 - a ⊗ ν`. Conjugating
`n = y(-1) x(1) y(-1)` by torus points gives `y(-c⁻¹) x(c) y(-c⁻¹) ν(c) = n` for every value
`c = a(t)`. Descent along the faithfully flat character `a : S ⟶ 𝔾_m` extends this to every
unit `c` on every test scheme. Group algebra then gives the rank-one relation
`x(X) y(Y) = y(Y/u) ν(u) x(X/u)`, `u = 1 + XY`, when `X` is a unit. Over a field `X` is zero or
a unit, and the published `RootCell.relationOver_of_isAlgClosed` gives the relation on every
test scheme.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.MaximalSplitSubgroup

open LocalSplitCell (rootPoint comp_rootPoint rootPoint_add rootPoint_neg rootPoint_zero)
open RankOneRootCellRelation (cu cu_mul cu_one cu_inv cu_neg cu_comp)

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The opposite line `t ↦ n⁻¹ x(-t) n` attached to a line `x` and a base point `n`. -/
def oppositeLine (x : RootCell.Ga k ⟶ G) (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    RootCell.Ga k ⟶ G :=
  LocalSplitCell.scaleHom (-1 : k) ≫ x ≫ (G.innerIso n⁻¹).hom

section Points

variable (x : RootCell.Ga k ⟶ G) (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)

theorem rootPoint_oppositeLine (Z : Over (Spec (CommRingCat.of k))) (c : Γ(Z.left, ⊤)) :
    rootPoint (oppositeLine x n) Z c =
      (G.constantPoint n Z)⁻¹ * rootPoint x Z (-c) * G.constantPoint n Z := by
  rw [oppositeLine, LocalSplitCell.rootPoint_scaleHom, rootPoint, Grp.comp_hom_hom,
    ← Category.assoc, comp_innerIso_hom, constantPoint_inv, inv_inv, map_neg, map_one,
    neg_one_mul]
  rfl

theorem mono_oppositeLine [Mono x.hom.hom] : Mono (oppositeLine x n).hom.hom := by
  have : IsIso (LocalSplitCell.scaleHom (-1 : k)).hom.hom := by
    have h := (inferInstance : IsIso (LocalSplitCell.scaleHom ((-1 : kˣ) : k)).hom.hom)
    simpa using h
  rw [oppositeLine, Grp.comp_hom_hom, Grp.comp_hom_hom]
  infer_instance

end Points

section Torus

variable (ν : cocharacterLattice S)

/-- The point `ν(c)` of the torus at a unit `c`. -/
def corootPoint {Z : Over (Spec (CommRingCat.of k))} (c : Γ(Z.left, ⊤)ˣ) : Z ⟶ S.X :=
  (Gm.pointsEquiv _ Z).symm c ≫ (CommGroupScheme.groupHom ν).hom.hom

variable {Z W : Over (Spec (CommRingCat.of k))}

theorem corootPoint_mul (c d : Γ(Z.left, ⊤)ˣ) :
    corootPoint ν (c * d) = corootPoint ν c * corootPoint ν d := by
  rw [corootPoint, corootPoint, corootPoint, map_mul, MonObj.mul_comp]

theorem corootPoint_one : corootPoint ν (1 : Γ(Z.left, ⊤)ˣ) = 1 := by
  rw [corootPoint, map_one, MonObj.one_comp]

theorem corootPoint_inv (c : Γ(Z.left, ⊤)ˣ) : corootPoint ν c⁻¹ = (corootPoint ν c)⁻¹ := by
  rw [corootPoint, corootPoint, map_inv, GrpObj.inv_comp]

theorem comp_corootPoint (f : W ⟶ Z) (c : Γ(Z.left, ⊤)ˣ) :
    f ≫ corootPoint ν c = corootPoint ν (Units.map f.left.appTop.hom.toMonoidHom c) := by
  rw [corootPoint, corootPoint, ← Category.assoc, RootCell.symm_pointsEquiv_comp]

theorem corootPoint_cu (a : characterLattice S) (t : Z ⟶ S.X) :
    corootPoint ν (cu a t) = t ≫ (CommGroupScheme.groupHom (a ≫ ν)).hom.hom := by
  rw [corootPoint, cu, MulEquiv.symm_apply_apply, comp_groupHom_comp]

variable {a : characterLattice S} (hpair : latticePairing S a ν = 2)

include hpair

theorem coroot_comp_root : ν ≫ a = (2 : ℤ) • 𝟙 (Gm (Spec (CommRingCat.of k))) := by
  rw [eq_gmEndEquiv_zsmul k (ν ≫ a)]
  exact congrArg (fun m : ℤ => m • 𝟙 (Gm (Spec (CommRingCat.of k)))) hpair

theorem cu_corootPoint (c : Γ(Z.left, ⊤)ˣ) : cu a (corootPoint ν c) = c * c := by
  have h2 := Gm.comp_zsmul_id ((Gm.pointsEquiv _ Z).symm c) 2
  rw [← coroot_comp_root ν hpair, comp_groupHom_comp] at h2
  rw [cu, corootPoint, h2, map_zpow, MulEquiv.apply_symm_apply, zpow_two]

theorem reflection_comp_root : (latticeReflectionIso a ν hpair).hom ≫ a = -a := by
  rw [latticeReflectionIso_hom, Preadditive.sub_comp, Category.id_comp, Category.assoc,
    coroot_comp_root ν hpair, Preadditive.comp_zsmul, Category.comp_id, two_smul]
  abel

theorem comp_reflection (t : Z ⟶ S.X) :
    t ≫ (CommGroupScheme.groupHom (latticeReflectionIso a ν hpair).hom).hom.hom =
      t * (corootPoint ν (cu a t))⁻¹ := by
  have hneg : t ≫ (CommGroupScheme.groupHom (-(a ≫ ν))).hom.hom =
      (t ≫ (CommGroupScheme.groupHom (a ≫ ν)).hom.hom)⁻¹ :=
    congrArg Additive.toMul ((evalPoint t).map_neg (a ≫ ν))
  have hid : t ≫ (CommGroupScheme.groupHom (𝟙 S)).hom.hom = t := by
    rw [show (CommGroupScheme.groupHom (𝟙 S)).hom.hom = 𝟙 S.X from rfl, Category.comp_id]
  rw [latticeReflectionIso_hom, sub_eq_add_neg, comp_groupHom_add, hneg, hid,
    corootPoint_cu]

theorem corootPoint_comp_reflection (c : Γ(Z.left, ⊤)ˣ) :
    corootPoint ν c ≫ (CommGroupScheme.groupHom (latticeReflectionIso a ν hpair).hom).hom.hom =
      (corootPoint ν c)⁻¹ := by
  rw [comp_reflection ν hpair, cu_corootPoint ν hpair, corootPoint_mul, mul_inv_rev,
    mul_inv_cancel_left]

theorem cu_comp_reflection (t : Z ⟶ S.X) :
    cu a (t ≫ (CommGroupScheme.groupHom (latticeReflectionIso a ν hpair).hom).hom.hom) =
      cu (-a) t := by
  rw [cu, cu, ← comp_groupHom_comp, reflection_comp_root ν hpair]

theorem reflection_comp_reflection :
    (latticeReflectionIso a ν hpair).hom ≫ (latticeReflectionIso a ν hpair).hom = 𝟙 S :=
  (latticeReflectionIso a ν hpair).hom_inv_id

end Torus

section Weyl

variable {i : S.toGrp ⟶ G} {a : characterLattice S} {ν : cocharacterLattice S}
  {hpair : latticePairing S a ν = 2} {x : RootCell.Ga k ⟶ G}
  {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
  (hn : IsNormalizingPoint i n (latticeReflectionIso a ν hpair))

variable {Z W : Over (Spec (CommRingCat.of k))}

include hn

theorem inv_conj_constantPoint (t : Z ⟶ S.X) :
    (G.constantPoint n Z)⁻¹ * (t ≫ i.hom.hom) * G.constantPoint n Z =
      (t ≫ (CommGroupScheme.groupHom (latticeReflectionIso a ν hpair).hom).hom.hom) ≫
        i.hom.hom := by
  have h := hn.conj_comp Z
    (t ≫ (CommGroupScheme.groupHom (latticeReflectionIso a ν hpair).hom).hom.hom)
  have hσ : (t ≫ (CommGroupScheme.groupHom (latticeReflectionIso a ν hpair).hom).hom.hom) ≫
      (CommGroupScheme.groupHom (latticeReflectionIso a ν hpair).hom).hom.hom = t := by
    rw [← comp_groupHom_comp, reflection_comp_reflection ν hpair]
    rfl
  rw [hσ] at h
  rw [← h]
  group

theorem isTorusEquivariant_oppositeLine (hx : VectorGroup.IsTorusEquivariant i x a) :
    VectorGroup.IsTorusEquivariant i (oppositeLine x n) (-a) := by
  intro Z t c
  change (t ≫ i.hom.hom) * rootPoint (oppositeLine x n) Z c * (t ≫ i.hom.hom)⁻¹ =
    rootPoint (oppositeLine x n) Z (VectorGroup.charValue (-a) Z t * c)
  rw [rootPoint_oppositeLine, rootPoint_oppositeLine]
  set N := G.constantPoint n Z
  set I := t ≫ i.hom.hom
  have hI : N * I * N⁻¹ =
      (t ≫ (CommGroupScheme.groupHom (latticeReflectionIso a ν hpair).hom).hom.hom) ≫
        i.hom.hom := hn.conj_comp Z t
  have hX := hx Z (t ≫ (CommGroupScheme.groupHom (latticeReflectionIso a ν hpair).hom).hom.hom)
    (-c)
  change _ * rootPoint x Z (-c) * _ = rootPoint x Z _ at hX
  rw [← hI, RankOneRootCellRelation.charValue_eq_cu, cu_comp_reflection ν hpair] at hX
  calc I * (N⁻¹ * rootPoint x Z (-c) * N) * I⁻¹
      = N⁻¹ * ((N * I * N⁻¹) * rootPoint x Z (-c) * (N * I * N⁻¹)⁻¹) * N := by group
    _ = N⁻¹ * rootPoint x Z (-(VectorGroup.charValue (-a) Z t * c)) * N := by
        rw [hX, RankOneRootCellRelation.charValue_eq_cu, mul_neg]

theorem conj_constantPoint_eq (t : Z ⟶ S.X) :
    (t ≫ i.hom.hom) * G.constantPoint n Z * (t ≫ i.hom.hom)⁻¹ =
      G.constantPoint n Z * (corootPoint ν (cu a t) ≫ i.hom.hom)⁻¹ := by
  have hc := inv_conj_constantPoint hn t
  rw [comp_reflection ν hpair, MonObj.mul_comp, GrpObj.inv_comp] at hc
  have hcomm : Commute (t ≫ i.hom.hom) (corootPoint ν (cu a t) ≫ i.hom.hom) := by
    change _ * _ = _ * _
    rw [← MonObj.mul_comp, ← MonObj.mul_comp, mul_comm]
  calc (t ≫ i.hom.hom) * G.constantPoint n Z * (t ≫ i.hom.hom)⁻¹
      = G.constantPoint n Z * ((G.constantPoint n Z)⁻¹ * (t ≫ i.hom.hom) *
          G.constantPoint n Z) * (t ≫ i.hom.hom)⁻¹ := by group
    _ = G.constantPoint n Z * ((t ≫ i.hom.hom) * (corootPoint ν (cu a t) ≫ i.hom.hom)⁻¹) *
          (t ≫ i.hom.hom)⁻¹ := by rw [hc]
    _ = G.constantPoint n Z * (corootPoint ν (cu a t) ≫ i.hom.hom)⁻¹ := by
        rw [(Commute.inv_right hcomm).eq]
        group

variable (hword : n = rootPoint (oppositeLine x n) (Over.mk (𝟙 _)) (-1) *
  rootPoint x (Over.mk (𝟙 _)) 1 * rootPoint (oppositeLine x n) (Over.mk (𝟙 _)) (-1))

omit hn in
include hword in
theorem constantPoint_eq_word (Z : Over (Spec (CommRingCat.of k))) :
    G.constantPoint n Z = rootPoint (oppositeLine x n) Z (-1) * rootPoint x Z 1 *
      rootPoint (oppositeLine x n) Z (-1) := by
  have h := congrArg (fun g => G.constantPoint g Z) hword
  simp only [constantPoint_mul] at h
  rw [h]
  simp only [GroupScheme.constantPoint, comp_rootPoint, map_neg, map_one]

include hword in
/-- **The Weyl identity at character values.** For every torus point `t` with `e = a(t)`,
`y(-e⁻¹) x(e) y(-e⁻¹) ν(e) = n`. -/
theorem weyl_cu (hx : VectorGroup.IsTorusEquivariant i x a) (t : Z ⟶ S.X) :
    rootPoint (oppositeLine x n) Z (-↑(cu a t)⁻¹) * rootPoint x Z ↑(cu a t) *
        rootPoint (oppositeLine x n) Z (-↑(cu a t)⁻¹) *
        (corootPoint ν (cu a t) ≫ i.hom.hom) = G.constantPoint n Z := by
  have hy := isTorusEquivariant_oppositeLine hn hx
  have hxe : (t ≫ i.hom.hom) * rootPoint x Z 1 * (t ≫ i.hom.hom)⁻¹ =
      rootPoint x Z ↑(cu a t) := by
    have h := hx Z t 1
    rw [RankOneRootCellRelation.charValue_eq_cu, mul_one] at h
    exact h
  have hye : (t ≫ i.hom.hom) * rootPoint (oppositeLine x n) Z (-1) * (t ≫ i.hom.hom)⁻¹ =
      rootPoint (oppositeLine x n) Z (-↑(cu a t)⁻¹) := by
    have h := hy Z t (-1)
    rw [RankOneRootCellRelation.charValue_eq_cu, cu_neg, mul_neg_one] at h
    exact h
  have hconj : (t ≫ i.hom.hom) * G.constantPoint n Z * (t ≫ i.hom.hom)⁻¹ =
      rootPoint (oppositeLine x n) Z (-↑(cu a t)⁻¹) * rootPoint x Z ↑(cu a t) *
        rootPoint (oppositeLine x n) Z (-↑(cu a t)⁻¹) := by
    rw [constantPoint_eq_word hword Z, ← hxe, ← hye]
    group
  rw [← hconj, conj_constantPoint_eq hn t]
  group

end Weyl

section Descent

variable (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (x : RootCell.Ga k ⟶ G)
  (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)

/-- The word `y(-c⁻¹) x(c) y(-c⁻¹) ν(c)` at a unit `c`, with `y = oppositeLine x n`. -/
def weylWord {Z : Over (Spec (CommRingCat.of k))} (c : Γ(Z.left, ⊤)ˣ) : Z ⟶ G.X :=
  rootPoint (oppositeLine x n) Z (-↑c⁻¹) * rootPoint x Z ↑c *
    rootPoint (oppositeLine x n) Z (-↑c⁻¹) * (corootPoint ν c ≫ i.hom.hom)

variable {Z W : Over (Spec (CommRingCat.of k))}

theorem comp_weylWord (f : W ⟶ Z) (c : Γ(Z.left, ⊤)ˣ) :
    f ≫ weylWord i ν x n c = weylWord i ν x n (Units.map f.left.appTop.hom.toMonoidHom c) := by
  simp only [weylWord, MonObj.comp_mul, comp_rootPoint, map_neg, ← Category.assoc,
    comp_corootPoint, RootCell.coe_units_map, RootCell.coe_units_map_inv]

/-- The universal unit on `𝔾_m`. -/
abbrev univUnit : Γ((Gm (Spec (CommRingCat.of k))).X.left, ⊤)ˣ :=
  Gm.pointsEquiv _ _ (𝟙 _)

theorem units_map_univUnit (Z : Over (Spec (CommRingCat.of k))) (c : Γ(Z.left, ⊤)ˣ) :
    Units.map ((Gm.pointsEquiv _ Z).symm c).left.appTop.hom.toMonoidHom (univUnit (k := k)) =
      c := by
  apply (Gm.pointsEquiv _ Z).symm.injective
  rw [RootCell.symm_pointsEquiv_comp, MulEquiv.symm_apply_apply, Category.comp_id]

theorem units_map_univUnit_character (a : characterLattice S) :
    Units.map (CommGroupScheme.groupHom a).hom.hom.left.appTop.hom.toMonoidHom
      (univUnit (k := k)) = cu a (𝟙 S.X) := by
  apply (Gm.pointsEquiv _ S.X).symm.injective
  rw [RootCell.symm_pointsEquiv_comp, MulEquiv.symm_apply_apply, Category.comp_id, cu,
    MulEquiv.symm_apply_apply, Category.id_comp]

variable {i ν x n} {a : characterLattice S} {hpair : latticePairing S a ν = 2}

/-- **The Weyl identity at every unit**, by fpqc descent along the character `a`. -/
theorem weylWord_eq (hT : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (hn : IsNormalizingPoint i n (latticeReflectionIso a ν hpair))
    (hword : n = rootPoint (oppositeLine x n) (Over.mk (𝟙 _)) (-1) *
      rootPoint x (Over.mk (𝟙 _)) 1 * rootPoint (oppositeLine x n) (Over.mk (𝟙 _)) (-1))
    (hx : VectorGroup.IsTorusEquivariant i x a) (c : Γ(Z.left, ⊤)ˣ) :
    weylWord i ν x n c = G.constantPoint n Z := by
  let q : S.X ⟶ (Gm (Spec (CommRingCat.of k))).X := (CommGroupScheme.groupHom a).hom.hom
  obtain ⟨-, hflat, hsurj⟩ := RelativeRoot.characterFpqc k S hT a ha
  have : Flat q.left := hflat
  have : Surjective q.left := hsurj
  have : Epi q.left := Flat.epi_of_flat_of_surjective _
  have : Epi q := Over.epi_of_epi_left _
  have h0 : weylWord i ν x n (univUnit (k := k)) =
      G.constantPoint n (Gm (Spec (CommRingCat.of k))).X := by
    apply (cancel_epi q).mp
    rw [comp_weylWord, G.constantPoint_naturality, units_map_univUnit_character]
    exact weyl_cu hn hword hx (𝟙 S.X)
  rw [← units_map_univUnit Z c, ← comp_weylWord, h0, G.constantPoint_naturality]

end Descent

/-- Over a field, every global function on the spectrum is zero or a unit. -/
theorem eq_zero_or_isUnit_of_field {K : Type u} [Field K]
    (z : Γ(Spec (CommRingCat.of K), ⊤)) : z = 0 ∨ IsUnit z := by
  let e := Scheme.ΓSpecIso (CommRingCat.of K)
  by_cases h : e.hom z = 0
  · left
    have hz : z = e.inv (e.hom z) := (Iso.hom_inv_id_apply e z).symm
    rw [hz, h, map_zero]
  · right
    have hu : IsUnit (e.hom z) := isUnit_iff_ne_zero.mpr h
    have := hu.map e.inv.hom
    rwa [show e.inv.hom (e.hom z) = z from Iso.hom_inv_id_apply e z] at this

section Relation

variable {i : S.toGrp ⟶ G} {a : characterLattice S} {ν : cocharacterLattice S}
  {hpair : latticePairing S a ν = 2} {x : RootCell.Ga k ⟶ G}
  {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
  (hn : IsNormalizingPoint i n (latticeReflectionIso a ν hpair))

variable {Z : Over (Spec (CommRingCat.of k))}

include hn in
theorem coroot_mul_constantPoint (c : Γ(Z.left, ⊤)ˣ) :
    (corootPoint ν c ≫ i.hom.hom) * G.constantPoint n Z =
      G.constantPoint n Z * (corootPoint ν c ≫ i.hom.hom)⁻¹ := by
  have h := hn.conj_comp Z (corootPoint ν c⁻¹)
  rw [corootPoint_comp_reflection ν hpair, corootPoint_inv, GrpObj.inv_comp, inv_inv] at h
  calc (corootPoint ν c ≫ i.hom.hom) * G.constantPoint n Z
      = (G.constantPoint n Z * (corootPoint ν c ≫ i.hom.hom)⁻¹ * (G.constantPoint n Z)⁻¹) *
          G.constantPoint n Z := by rw [h]
    _ = _ := by group

include hpair in
theorem coroot_conj_line (hx : VectorGroup.IsTorusEquivariant i x a) (c : Γ(Z.left, ⊤)ˣ)
    (d : Γ(Z.left, ⊤)) :
    (corootPoint ν c ≫ i.hom.hom) * rootPoint x Z d * (corootPoint ν c ≫ i.hom.hom)⁻¹ =
      rootPoint x Z (↑c * ↑c * d) := by
  have h := hx Z (corootPoint ν c) d
  rw [RankOneRootCellRelation.charValue_eq_cu, cu_corootPoint ν hpair, Units.val_mul] at h
  exact h

include hn in
theorem coroot_conj_oppositeLine (hx : VectorGroup.IsTorusEquivariant i x a)
    (c : Γ(Z.left, ⊤)ˣ) (d : Γ(Z.left, ⊤)) :
    (corootPoint ν c ≫ i.hom.hom) * rootPoint (oppositeLine x n) Z d *
        (corootPoint ν c ≫ i.hom.hom)⁻¹ =
      rootPoint (oppositeLine x n) Z (↑(c * c)⁻¹ * d) := by
  have h := isTorusEquivariant_oppositeLine hn hx Z (corootPoint ν c) d
  rw [RankOneRootCellRelation.charValue_eq_cu, cu_neg, cu_corootPoint ν hpair] at h
  exact h

variable (hT : IsSplitTorus S.toGrp) (ha : a ≠ 0)
  (hword : n = rootPoint (oppositeLine x n) (Over.mk (𝟙 _)) (-1) *
    rootPoint x (Over.mk (𝟙 _)) 1 * rootPoint (oppositeLine x n) (Over.mk (𝟙 _)) (-1))
  (hx : VectorGroup.IsTorusEquivariant i x a)

include hT ha hn hword hx

theorem constantPoint_mul_self :
    G.constantPoint n Z * G.constantPoint n Z = corootPoint ν (-1 : Γ(Z.left, ⊤)ˣ) ≫ i.hom.hom := by
  have h1 := weylWord_eq hT ha hn hword hx (1 : Γ(Z.left, ⊤)ˣ)
  have h2 := weylWord_eq hT ha hn hword hx (-1 : Γ(Z.left, ⊤)ˣ)
  simp only [weylWord, inv_one, Units.val_one, corootPoint_one, MonObj.one_comp, mul_one,
    rootPoint_neg] at h1
  simp only [weylWord, inv_neg, inv_one, Units.val_neg, Units.val_one, neg_neg,
    rootPoint_neg] at h2
  have h1' : rootPoint (oppositeLine x n) Z 1 * (rootPoint x Z 1)⁻¹ *
      rootPoint (oppositeLine x n) Z 1 = (G.constantPoint n Z)⁻¹ := by
    rw [← h1]
    group
  rw [h1'] at h2
  calc G.constantPoint n Z * G.constantPoint n Z
      = G.constantPoint n Z * ((G.constantPoint n Z)⁻¹ *
          (corootPoint ν (-1 : Γ(Z.left, ⊤)ˣ) ≫ i.hom.hom)) := by rw [h2]
    _ = _ := by group

/-- **The rank-one relation when the first coordinate is a unit.** -/
theorem relation_of_isUnit (e u : Γ(Z.left, ⊤)ˣ) (c : Γ(Z.left, ⊤))
    (hu : (u : Γ(Z.left, ⊤)) = 1 + ↑e * c) :
    rootPoint x Z ↑e * rootPoint (oppositeLine x n) Z c =
      rootPoint (oppositeLine x n) Z (↑u⁻¹ * c) * (corootPoint ν u ≫ i.hom.hom) *
        rootPoint x Z (↑u⁻¹ * ↑e) := by
  have he := weylWord_eq hT ha hn hword hx e
  have hd := weylWord_eq hT ha hn hword hx (-(e * u⁻¹))
  simp only [weylWord] at he hd
  have heu : (↑e : Γ(Z.left, ⊤)) * ↑e⁻¹ = 1 := Units.mul_inv e
  have huu : (↑u : Γ(Z.left, ⊤)) * ↑u⁻¹ = 1 := Units.mul_inv u
  have hdval : (↑(-(e * u⁻¹)) : Γ(Z.left, ⊤)) = -(↑u⁻¹ * ↑e) := by
    simp only [Units.val_neg, Units.val_mul]
    ring
  have hdinvval : (↑(-(e * u⁻¹))⁻¹ : Γ(Z.left, ⊤)) = -(↑u * ↑e⁻¹) := by
    simp only [inv_neg, mul_inv_rev, inv_inv, Units.val_neg, Units.val_mul]
  -- `x(e) = y(e⁻¹) n ν(e)⁻¹ y(e⁻¹)`.
  have hxe : rootPoint x Z ↑e =
      rootPoint (oppositeLine x n) Z ↑e⁻¹ * G.constantPoint n Z *
        (corootPoint ν e ≫ i.hom.hom)⁻¹ * rootPoint (oppositeLine x n) Z ↑e⁻¹ := by
    rw [← he]
    simp only [rootPoint_neg]
    group
  -- `y(-d⁻¹) = n ν(d)⁻¹ y(d⁻¹) x(-d)` for `d = -(e u⁻¹)`.
  have hyd : rootPoint (oppositeLine x n) Z (-↑(-(e * u⁻¹))⁻¹) =
      G.constantPoint n Z * (corootPoint ν (-(e * u⁻¹)) ≫ i.hom.hom)⁻¹ *
        rootPoint (oppositeLine x n) Z ↑(-(e * u⁻¹))⁻¹ * rootPoint x Z (-↑(-(e * u⁻¹))) := by
    rw [← hd]
    simp only [rootPoint_neg]
    group
  have hdinv : -(↑(-(e * u⁻¹))⁻¹ : Γ(Z.left, ⊤)) = ↑e⁻¹ + c := by
    rw [hdinvval, neg_neg]
    linear_combination (↑e⁻¹ : Γ(Z.left, ⊤)) * hu + c * heu
  rw [hdinv] at hyd
  have hNN := constantPoint_mul_self hn hT ha hword hx (Z := Z)
  have hHN (c : Γ(Z.left, ⊤)ˣ) : (corootPoint ν c ≫ i.hom.hom)⁻¹ * G.constantPoint n Z =
      G.constantPoint n Z * (corootPoint ν c ≫ i.hom.hom) := by
    have h := coroot_mul_constantPoint hn c⁻¹
    simp only [corootPoint_inv, GrpObj.inv_comp, inv_inv] at h
    exact h
  have hHu : G.constantPoint n Z * (corootPoint ν e ≫ i.hom.hom)⁻¹ * G.constantPoint n Z *
      (corootPoint ν (-(e * u⁻¹)) ≫ i.hom.hom)⁻¹ = corootPoint ν u ≫ i.hom.hom := by
    have h1 : G.constantPoint n Z * (corootPoint ν e ≫ i.hom.hom)⁻¹ * G.constantPoint n Z *
        (corootPoint ν (-(e * u⁻¹)) ≫ i.hom.hom)⁻¹ =
        (G.constantPoint n Z * G.constantPoint n Z) *
          ((corootPoint ν e ≫ i.hom.hom) * (corootPoint ν (-(e * u⁻¹)) ≫ i.hom.hom)⁻¹) := by
      rw [mul_assoc (G.constantPoint n Z), hHN e]
      group
    have h2 : (-1 : Γ(Z.left, ⊤)ˣ) * (e * (-(e * u⁻¹))⁻¹) = u := by
      ext
      simp only [inv_neg, mul_inv_rev, inv_inv, Units.val_neg, Units.val_mul, Units.val_one]
      linear_combination (↑u : Γ(Z.left, ⊤)) * heu
    have h3 : (corootPoint ν (-1 : Γ(Z.left, ⊤)ˣ) ≫ i.hom.hom) *
        ((corootPoint ν e ≫ i.hom.hom) * (corootPoint ν (-(e * u⁻¹)) ≫ i.hom.hom)⁻¹) =
        corootPoint ν ((-1 : Γ(Z.left, ⊤)ˣ) * (e * (-(e * u⁻¹))⁻¹)) ≫ i.hom.hom := by
      rw [corootPoint_mul, corootPoint_mul, corootPoint_inv, MonObj.mul_comp, MonObj.mul_comp,
        GrpObj.inv_comp]
    rw [h1, hNN, h3, h2]
  have hC := coroot_conj_oppositeLine hn hx u (↑(-(e * u⁻¹))⁻¹)
  have hA : (↑e⁻¹ : Γ(Z.left, ⊤)) + ↑(u * u)⁻¹ * ↑(-(e * u⁻¹))⁻¹ = ↑u⁻¹ * c := by
    rw [hdinvval, mul_inv_rev, Units.val_mul]
    linear_combination (↑e⁻¹ * ↑u⁻¹ : Γ(Z.left, ⊤)) * hu - (↑e⁻¹ + ↑u⁻¹ * ↑e⁻¹) * huu +
      (↑u⁻¹ * c) * heu
  calc rootPoint x Z ↑e * rootPoint (oppositeLine x n) Z c
      = rootPoint (oppositeLine x n) Z ↑e⁻¹ * G.constantPoint n Z *
          (corootPoint ν e ≫ i.hom.hom)⁻¹ *
          (rootPoint (oppositeLine x n) Z ↑e⁻¹ * rootPoint (oppositeLine x n) Z c) := by
        rw [hxe]
        group
    _ = rootPoint (oppositeLine x n) Z ↑e⁻¹ *
          (G.constantPoint n Z * (corootPoint ν e ≫ i.hom.hom)⁻¹ * G.constantPoint n Z *
            (corootPoint ν (-(e * u⁻¹)) ≫ i.hom.hom)⁻¹) *
          rootPoint (oppositeLine x n) Z ↑(-(e * u⁻¹))⁻¹ *
          rootPoint x Z (-↑(-(e * u⁻¹))) := by
        rw [← rootPoint_add, hyd]
        group
    _ = rootPoint (oppositeLine x n) Z ↑e⁻¹ *
          ((corootPoint ν u ≫ i.hom.hom) * rootPoint (oppositeLine x n) Z ↑(-(e * u⁻¹))⁻¹ *
            (corootPoint ν u ≫ i.hom.hom)⁻¹) * (corootPoint ν u ≫ i.hom.hom) *
          rootPoint x Z (-↑(-(e * u⁻¹))) := by
        rw [hHu]
        group
    _ = rootPoint (oppositeLine x n) Z (↑u⁻¹ * c) * (corootPoint ν u ≫ i.hom.hom) *
          rootPoint x Z (↑u⁻¹ * ↑e) := by
        rw [hC, ← rootPoint_add, hA, hdval, neg_neg]

/-- **The rank-one relation over a field.** -/
theorem relationOver_field {K : Type u} [Field K] (f : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) :
    RootCell.RelationOver i ν x (oppositeLine x n) (Over.mk f) := by
  intro p q p' q' u hu hp hq
  change (p ≫ x.hom.hom) * (q ≫ (oppositeLine x n).hom.hom) =
    (q' ≫ (oppositeLine x n).hom.hom) * (corootPoint ν u ≫ i.hom.hom) * (p' ≫ x.hom.hom)
  rw [LocalSplitCell.comp_eq_rootPoint x p, LocalSplitCell.comp_eq_rootPoint x p',
    LocalSplitCell.comp_eq_rootPoint (oppositeLine x n) q,
    LocalSplitCell.comp_eq_rootPoint (oppositeLine x n) q']
  change rootPoint x _ (RootCell.crd p) * rootPoint (oppositeLine x n) _ (RootCell.crd q) =
    rootPoint (oppositeLine x n) _ (RootCell.crd q') * (corootPoint ν u ≫ i.hom.hom) *
      rootPoint x _ (RootCell.crd p')
  rw [hp, hq]
  have hcases : RootCell.crd p = 0 ∨ IsUnit (RootCell.crd p : Γ((Over.mk f).left, ⊤)) :=
    eq_zero_or_isUnit_of_field (K := K) (RootCell.crd p)
  rcases hcases with h0 | ⟨e, he⟩
  · have hu1 : u = 1 := by
      ext
      rw [hu, h0, zero_mul, add_zero, Units.val_one]
    rw [h0, hu1, mul_zero, rootPoint_zero, corootPoint_one, MonObj.one_comp, inv_one,
      Units.val_one, one_mul]
    group
  · rw [← he] at hu ⊢
    exact relation_of_isUnit hn hT ha hword hx e u (RootCell.crd q) hu

/-- **The rank-one relation on every test scheme.** -/
theorem relationOver [IsSeparated G.X.hom] (Z : Over (Spec (CommRingCat.of k))) :
    RootCell.RelationOver i ν x (oppositeLine x n) Z :=
  RootCell.relationOver_of_isAlgClosed
    (fun _ _ _ f => relationOver_field hn hT ha hword hx f) Z

end Relation

section Reflection

variable {a : characterLattice S} {ν : cocharacterLattice S} (hpair : latticePairing S a ν = 2)

/-- The reflection on cocharacters: `ξ ∘ s_a = ξ - ⟨a, ξ⟩ ν`. -/
theorem cocharacter_comp_reflection (ξ : cocharacterLattice S) :
    ξ ≫ (latticeReflectionIso a ν hpair).hom = ξ - latticePairing S a ξ • ν := by
  rw [latticeReflectionIso_hom, Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
    eq_gmEndEquiv_zsmul k (ξ ≫ a), Preadditive.zsmul_comp, Category.id_comp]
  rfl

/-- The reflection fixes every cocharacter orthogonal to `a`. -/
theorem groupHom_comp_reflection_of_pairing_eq_zero (ξ : cocharacterLattice S)
    (hξ : latticePairing S a ξ = 0) :
    CommGroupScheme.groupHom ξ ≫ CommGroupScheme.groupHom (latticeReflectionIso a ν hpair).hom =
      CommGroupScheme.groupHom ξ := by
  change CommGroupScheme.groupHom (ξ ≫ (latticeReflectionIso a ν hpair).hom) = _
  rw [cocharacter_comp_reflection hpair, hξ, zero_smul, sub_zero]

/-- The reflection on characters: `s_a^* χ = χ - ⟨χ, ν⟩ a`, through the inverse. -/
theorem reflection_inv_comp_character (χ : characterLattice S) :
    (latticeReflectionIso a ν hpair).inv ≫ χ = χ - latticePairing S χ ν • a :=
  characterAut_latticeReflectionIso a ν hpair χ

end Reflection

section Main

theorem rootPoint_one_ne_one (x : RootCell.Ga k ⟶ G) [Mono x.hom.hom] :
    rootPoint x (Over.mk (𝟙 (Spec (CommRingCat.of k)))) 1 ≠ 1 := by
  intro h
  rw [← rootPoint_zero x (Over.mk (𝟙 _))] at h
  have h' := (cancel_mono x.hom.hom).mp h
  have hc := congrArg
    (fun z => (VectorGroup.coordinates (CommRingCat.of k) 1 _ z).toAdd 0) h'
  simp only [VectorGroup.coordinates_scalarPoint] at hc
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom hc
  rw [map_one, map_zero] at this
  exact one_ne_zero this

variable [IsAffineHom G.X.hom]

/-- **Rank-one data for an equivariant line in a nonmultipliable root group.** Let `i` be a
maximal split torus of a connected reductive group, `a` a relative root with `2a` not a
root, and `x` a monic `a`-equivariant line in the root group `U_(a)`. There are a
cocharacter `ν` with `⟨a, ν⟩ = 2` and a rational point `n`, namely
`n = y(-1) x(1) y(-1)` for the opposite line `y(t) = n⁻¹ x(-t) n`, such that `y` is a monic
`-a`-equivariant line in `U_(-a)` and `n` normalizes the torus through the reflection
`s_a = 1 - a ⊗ ν`. On every test scheme, `x`, `y` and `ν` satisfy the rank-one relation
`x(X) y(Y) = y(Y/u) ν(u) x(X/u)` for `u = 1 + XY` a unit. -/
theorem exists_rankOneRelation (hG : IsConnectedReductive G) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) {a : characterLattice S} (ha : a ∈ roots i)
    (h2 : (2 : ℤ) • a ∉ roots i) (x : RootCell.Ga k ⟶ G)
    (hx : VectorGroup.IsTorusEquivariant i x a) [Mono x.hom.hom]
    (hxr : SubgroupFunctor.range x ≤ RelativeRoot.subgroup i a) :
    ∃ (ν : cocharacterLattice S) (hpair : latticePairing S a ν = 2)
      (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X),
      VectorGroup.IsTorusEquivariant i (oppositeLine x n) (-a) ∧
      Mono (oppositeLine x n).hom.hom ∧
      SubgroupFunctor.range (oppositeLine x n) ≤ RelativeRoot.subgroup i (-a) ∧
      n = rootPoint (oppositeLine x n) (Over.mk (𝟙 _)) (-1) * rootPoint x (Over.mk (𝟙 _)) 1 *
        rootPoint (oppositeLine x n) (Over.mk (𝟙 _)) (-1) ∧
      IsNormalizingPoint i n (latticeReflectionIso a ν hpair) ∧
      ∀ Z : Over (Spec (CommRingCat.of k)), RootCell.RelationOver i ν x (oppositeLine x n) Z := by
  have : Mono i.hom.hom.left := hi.1.mono
  have hT : IsSplitTorus S.toGrp := hi.1.1
  have ha0 : a ≠ 0 := ha.1
  let u : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := rootPoint x (Over.mk (𝟙 _)) 1
  have hu : u ∈ (RelativeRoot.subgroup i a).carrier (Over.mk (𝟙 _)) :=
    hxr _ (SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩)
  have hu1 : u ≠ 1 := rootPoint_one_ne_one x
  have hfac := rootRankOneFactorization k G hG S i hi a ha u hu hu1
  obtain ⟨p, hp, -⟩ := hfac.1
  obtain ⟨-, -, -, h2p⟩ := hfac.2 p hp
  obtain ⟨hp12, hp1, -⟩ := h2p h2
  let n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := p.1 * u * p.2
  let nN : normalizerPoints i := ⟨n, hp.2.2⟩
  obtain ⟨hpair, hrefl⟩ := hp.coroot_spec i hT ha0 hu hu1
  set ν := hp.coroot i hT ha0 hu hu1
  have hσ : normalizingAut i nN = latticeReflectionIso a ν hpair := by
    apply hT.iso_ext_of_character_congr
    ext χ
    rw [characterLattice.congr_apply, characterLattice.congr_apply, ← weylAction_apply, hrefl,
      reflection_inv_comp_character]
  have hn : IsNormalizingPoint i n (latticeReflectionIso a ν hpair) := by
    rw [← hσ]
    exact isNormalizingPoint_normalizingAut i nN
  have hy1 : rootPoint (oppositeLine x n) (Over.mk (𝟙 _)) (-1) = p.1 := by
    rw [rootPoint_oppositeLine, neg_neg, G.constantPoint_self, hp1]
  have hword : n = rootPoint (oppositeLine x n) (Over.mk (𝟙 _)) (-1) *
      rootPoint x (Over.mk (𝟙 _)) 1 * rootPoint (oppositeLine x n) (Over.mk (𝟙 _)) (-1) := by
    rw [hy1]
    exact congrArg (fun q => p.1 * u * q) hp12.symm
  have hwa : weylAction i nN⁻¹ a = -a := by
    have h1 : weylAction i nN a = -a := by
      rw [hrefl, hpair, two_smul]
      abel
    calc weylAction i nN⁻¹ a = weylAction i nN⁻¹ (weylAction i nN (-a)) := by
          rw [map_neg, h1, neg_neg]
      _ = -a := by
          rw [map_inv]
          exact (weylAction i nN).symm_apply_apply (-a)
  have hrange : SubgroupFunctor.range (oppositeLine x n) ≤ RelativeRoot.subgroup i (-a) := by
    intro Z z hz
    obtain ⟨w, rfl⟩ := SubgroupFunctor.mem_range.mp hz
    rw [LocalSplitCell.comp_eq_rootPoint, rootPoint_oppositeLine]
    have hg : rootPoint x Z (-LocalSplitCell.gaCoord w) ∈
        (RelativeRoot.subgroup i a).carrier Z :=
      hxr _ (SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩)
    have h := RelativeRoot.normalizer_conj_mem i a nN⁻¹ hg
    rw [hwa] at h
    simp only [Subgroup.coe_inv, constantPoint_inv, inv_inv] at h
    exact h
  exact ⟨ν, hpair, n, isTorusEquivariant_oppositeLine hn hx, mono_oppositeLine x n, hrange,
    hword, hn, fun Z => relationOver hn hT ha0 hword hx Z⟩

end Main

end Langlands.GroupScheme.MaximalSplitSubgroup
