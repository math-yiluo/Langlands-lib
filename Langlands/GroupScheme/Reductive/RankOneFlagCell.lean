import Langlands.GroupScheme.Absolute.TripleCell
import Langlands.GroupScheme.Dynamic.SchemeActionLimit
import Langlands.GroupScheme.Dynamic.LimitMap
import Langlands.GroupScheme.Dynamic.LeviCocharacterCombination
import Langlands.GroupScheme.Dynamic.NormalizedLimits
import Langlands.GroupScheme.StabilizerClosedSubgroup
import Langlands.GroupScheme.Chevalley.UnipotentOrbit
import Langlands.GroupScheme.SchemeActionRationalOrbit
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Langlands.GroupScheme.Dynamic.TwoSidedConstancy
import Langlands.GroupScheme.Dynamic.GmOrbitInversion
import Langlands.GroupScheme.Dynamic.OppositeBaseChange
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # The open cell through a fixed point of a homogeneous space

Let a smooth affine group `G` over an algebraically closed field act on a separated
scheme `X`, and let `x` be a rational point fixed by the centralizer `Z(χ)` and by the dynamic
unipotent `U(χ)` of a cocharacter `χ`. The image `Y` of the open cell
`U(-χ) · Z(χ) · U(χ)` under the orbit map of `x` is open when the orbit map is flat and locally
of finite presentation, and it is the image of `U(-χ)`. See the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RankOneFlagCell

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {X : Over (Spec (CommRingCat.of k))}
  (a : SchemeAction G X) (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X)
  {M Z U : GroupScheme (Spec (CommRingCat.of k))} (iM : M ⟶ G) (iZ : Z ⟶ G) (iU : U ⟶ G)

/-- The rational base point `Spec k` over `Spec k`. -/
abbrev pt' (k : Type u) [Field k] : Over (Spec (CommRingCat.of k)) :=
  Over.mk (𝟙 (Spec (CommRingCat.of k)))

/-- The orbit map of `x` restricted to the first cell factor `M`. -/
def cellOrbit : M.X ⟶ X :=
  iM.hom.hom ≫ a.orbitMap x

/-- On the triple cell, the orbit map of a point fixed by the last two factors only sees the
first factor. -/
theorem tripleCell_comp_orbitMap (hZ : (a.restrict iZ).IsFixed x)
    (hU : (a.restrict iU).IsFixed x) :
    Dynamic.tripleCellMultiplication iM iZ iU ≫ a.orbitMap x =
      fst M.X (Z.X ⊗ U.X) ≫ cellOrbit a x iM := by
  have h1 : 𝟙 (M.X ⊗ (Z.X ⊗ U.X)) = lift (fst M.X (Z.X ⊗ U.X))
      (lift (snd M.X (Z.X ⊗ U.X) ≫ fst Z.X U.X) (snd M.X (Z.X ⊗ U.X) ≫ snd Z.X U.X)) := by
    ext <;> simp
  rw [← Category.id_comp (Dynamic.tripleCellMultiplication iM iZ iU), h1,
    Dynamic.lift_tripleCellMultiplication, a.comp_orbitMap, cellOrbit,
    ← Category.assoc, a.comp_orbitMap, a.act_mul, a.act_mul]
  have hv := hU _ (toUnit (M.X ⊗ (Z.X ⊗ U.X))) (snd M.X (Z.X ⊗ U.X) ≫ snd Z.X U.X)
  rw [SchemeAction.restrict_act] at hv
  have hz := hZ _ (toUnit (M.X ⊗ (Z.X ⊗ U.X))) (snd M.X (Z.X ⊗ U.X) ≫ fst Z.X U.X)
  rw [SchemeAction.restrict_act] at hz
  rw [hv, hz]

/-- The first projection of the triple cell has a section. -/
theorem range_fst_comp {W : Scheme.{u}} (f : M.X.left ⟶ W) :
    Set.range ((fst M.X (Z.X ⊗ U.X)).left ≫ f) = Set.range f := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    exact ⟨_, rfl⟩
  · rintro _ ⟨p, rfl⟩
    let s : M.X ⟶ M.X ⊗ (Z.X ⊗ U.X) := lift (𝟙 M.X) (lift (1 : M.X ⟶ Z.X) (1 : M.X ⟶ U.X))
    refine ⟨s.left p, ?_⟩
    have hs : s ≫ fst M.X (Z.X ⊗ U.X) = 𝟙 M.X := lift_fst _ _
    change (s.left ≫ (fst M.X (Z.X ⊗ U.X)).left ≫ f) p = f p
    rw [← Category.assoc, ← Over.comp_left, hs, Over.id_left, Category.id_comp]

/-- The orbit along the opposite cocharacter is the orbit precomposed with inversion. -/
theorem gmOrbit_opposite (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {W : Over (Spec (CommRingCat.of k))} (w : W ⟶ X) :
    (a.restrict (Dynamic.oppositeCocharacter χ)).gmOrbit w =
      W ◁ ι[(Gm (Spec (CommRingCat.of k))).X] ≫ (a.restrict χ).gmOrbit w := by
  simp only [SchemeAction.gmOrbit, SchemeAction.restrict_act]
  rw [a.naturality, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, Dynamic.oppositeCocharacter,
    Grp.comp_hom_hom, ← Category.assoc, Dynamic.comp_powerHom, zpow_neg_one]
  rfl

section Restrict

variable {K L : GroupScheme (Spec (CommRingCat.of k))} (f : K ⟶ L) (g : L ⟶ G)

/-- Restricting an action twice acts as restricting along the composite. -/
theorem restrict_restrict_act {W : Over (Spec (CommRingCat.of k))} (h : W ⟶ K.X) (y : W ⟶ X) :
    ((a.restrict g).restrict f).act h y = (a.restrict (f ≫ g)).act h y := by
  simp only [SchemeAction.restrict_act, Grp.comp_hom_hom, Category.assoc]

theorem isFixed_restrict_restrict_iff {W : Over (Spec (CommRingCat.of k))} (y : W ⟶ X) :
    ((a.restrict g).restrict f).IsFixed y ↔ (a.restrict (f ≫ g)).IsFixed y := by
  simp only [SchemeAction.IsFixed, restrict_restrict_act]

theorem gmOrbit_restrict_restrict (f : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ L)
    {W : Over (Spec (CommRingCat.of k))} (y : W ⟶ X) :
    ((a.restrict g).restrict f).gmOrbit y = (a.restrict (f ≫ g)).gmOrbit y := by
  simp only [SchemeAction.gmOrbit, restrict_restrict_act]

theorem isGmOrbitExtension_restrict_restrict_iff (f : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ L)
    {W : Over (Spec (CommRingCat.of k))} (y : W ⟶ X)
    (e : W ⊗ AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ X) :
    ((a.restrict g).restrict f).IsGmOrbitExtension y e ↔
      (a.restrict (f ≫ g)).IsGmOrbitExtension y e := by
  simp only [SchemeAction.IsGmOrbitExtension, gmOrbit_restrict_restrict]

end Restrict

omit [Field k] in
/-- The limit of a fixed point is the point itself. -/
theorem evalZero_eq_of_isFixed {S : Scheme.{u}} {Y : Over S} [IsSeparated Y.hom]
    (b : SchemeAction (Gm S).toGrp Y) {W : Over S} {w : W ⟶ Y} (hw : b.IsFixed w)
    {e : W ⊗ AffineLine.scheme S ⟶ Y} (he : b.IsGmOrbitExtension w e) :
    Dynamic.evalZero e = w := by
  have hc : b.IsGmOrbitExtension w (fst W (AffineLine.scheme S) ≫ w) := by
    rw [SchemeAction.IsGmOrbitExtension, whiskerLeft_fst_assoc, SchemeAction.gmOrbit]
    exact (hw _ (fst W (Gm S).X) (snd W (Gm S).X)).symm
  rw [he.unique b hc, Dynamic.evalZero_fst]

/-- **Open cell data through `x`.** A cocharacter `χ`, closed subgroups representing
`U(-χ)`, `Z(χ)` and `U(χ)`, with `x` fixed by the last two, and the triple cell open. -/
structure Cell where
  χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G
  M : GroupScheme (Spec (CommRingCat.of k))
  Z : GroupScheme (Spec (CommRingCat.of k))
  U : GroupScheme (Spec (CommRingCat.of k))
  iM : M ⟶ G
  iZ : Z ⟶ G
  iU : U ⟶ G
  hM : (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).IsRepresentedBy iM
  hZ : (Dynamic.centralizer χ).IsRepresentedBy iZ
  hU : (Dynamic.unipotent χ).IsRepresentedBy iU
  fixZ : (a.restrict iZ).IsFixed x
  fixU : (a.restrict iU).IsFixed x
  isOpenImmersion : IsOpenImmersion (Dynamic.tripleCellMultiplication iM iZ iU).left

namespace Cell

variable {a x} (C : Cell a x)

/-- The triple cell `U(-χ) × Z(χ) × U(χ)`. -/
abbrev Ω : Over (Spec (CommRingCat.of k)) := C.M.X ⊗ (C.Z.X ⊗ C.U.X)

/-- The orbit map of `x` on the triple cell. -/
def cellMap : C.Ω ⟶ X :=
  Dynamic.tripleCellMultiplication C.iM C.iZ C.iU ≫ a.orbitMap x

theorem cellMap_eq : C.cellMap = fst C.M.X (C.Z.X ⊗ C.U.X) ≫ cellOrbit a x C.iM :=
  tripleCell_comp_orbitMap a x C.iM C.iZ C.iU C.fixZ C.fixU

theorem range_cellMap : Set.range C.cellMap.left = Set.range (cellOrbit a x C.iM).left := by
  rw [cellMap_eq, Over.comp_left, range_fst_comp]

/-- Points of the centralizer of `χ` fix `x`. -/
theorem act_eq_of_mem_centralizer {W : Over (Spec (CommRingCat.of k))} {g : W ⟶ G.X}
    (hg : g ∈ (Dynamic.centralizer C.χ).carrier W) :
    a.act g (toUnit W ≫ x) = toUnit W ≫ x := by
  rw [← C.hZ.2] at hg
  obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  have h := C.fixZ W (toUnit W) z
  rwa [SchemeAction.restrict_act] at h

/-- Points of the centralizer of `χ` normalize the first factor `U(-χ)`. -/
theorem exists_conj_of_mem_centralizer {W : Over (Spec (CommRingCat.of k))} {g : W ⟶ G.X}
    (hg : g ∈ (Dynamic.centralizer C.χ).carrier W) (m : W ⟶ C.M.X) :
    ∃ m' : W ⟶ C.M.X, m' ≫ C.iM.hom.hom = g * (m ≫ C.iM.hom.hom) * g⁻¹ := by
  have hg' : g ∈ (Dynamic.parabolic (Dynamic.oppositeCocharacter C.χ)).carrier W :=
    Dynamic.centralizer_le_parabolic _ _
      (Dynamic.centralizer_le_precomp C.χ
        (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1))) W hg)
  have hm : m ≫ C.iM.hom.hom ∈
      (Dynamic.unipotent (Dynamic.oppositeCocharacter C.χ)).carrier W := by
    rw [← C.hM.2]
    exact SubgroupFunctor.mem_range.mpr ⟨m, rfl⟩
  have h := Dynamic.conj_mem_unipotent _ hg' hm
  rw [← C.hM.2] at h
  exact SubgroupFunctor.mem_range.mp h

/-- Acting by a centralizing point on a point of the cell image stays in the cell image. -/
theorem exists_act_cellOrbit {W : Over (Spec (CommRingCat.of k))} {g : W ⟶ G.X}
    (hg : g ∈ (Dynamic.centralizer C.χ).carrier W) (m : W ⟶ C.M.X) :
    ∃ m' : W ⟶ C.M.X, a.act g (m ≫ cellOrbit a x C.iM) = m' ≫ cellOrbit a x C.iM := by
  obtain ⟨m', hm'⟩ := C.exists_conj_of_mem_centralizer hg m
  refine ⟨m', ?_⟩
  rw [cellOrbit, ← Category.assoc, a.comp_orbitMap, ← Category.assoc, a.comp_orbitMap]
  calc a.act g (a.act (m ≫ C.iM.hom.hom) (toUnit W ≫ x))
      = a.act (g * (m ≫ C.iM.hom.hom) * g⁻¹ * g) (toUnit W ≫ x) := by
        rw [inv_mul_cancel_right, a.act_mul]
    _ = a.act (m' ≫ C.iM.hom.hom) (toUnit W ≫ x) := by
        rw [a.act_mul, C.act_eq_of_mem_centralizer hg, hm']

variable [Flat (a.orbitMap x).left] [LocallyOfFinitePresentation (a.orbitMap x).left]

instance : IsOpenImmersion (Dynamic.tripleCellMultiplication C.iM C.iZ C.iU).left :=
  C.isOpenImmersion

instance : Flat C.cellMap.left := by
  rw [cellMap, Over.comp_left]; infer_instance

instance : LocallyOfFinitePresentation C.cellMap.left := by
  rw [cellMap, Over.comp_left]; infer_instance

/-- **The open cell through `x`.** The image of the first cell factor under the orbit map. -/
def opens : X.left.Opens :=
  ⟨Set.range (cellOrbit a x C.iM).left, by
    rw [← C.range_cellMap]
    have : UniversallyOpen C.cellMap.left := UniversallyOpen.of_flat _
    exact C.cellMap.left.isOpenMap.isOpen_range⟩

/-- The open cell as a scheme over `k`. -/
def scheme : Over (Spec (CommRingCat.of k)) :=
  Over.mk (C.opens.ι ≫ X.hom)

/-- The inclusion of the open cell. -/
def incl : C.scheme ⟶ X :=
  Over.homMk C.opens.ι rfl

instance : IsOpenImmersion C.incl.left :=
  inferInstanceAs (IsOpenImmersion C.opens.ι)

instance : Mono C.incl :=
  Over.mono_of_mono_left _

theorem range_incl : Set.range C.incl.left = C.opens :=
  C.opens.range_ι

/-- A morphism whose image lies in the open cell factors through it. -/
def lift {W : Over (Spec (CommRingCat.of k))} (f : W ⟶ X)
    (hf : Set.range f.left ⊆ C.opens) : W ⟶ C.scheme :=
  Over.homMk (show W.left ⟶ C.opens.toScheme from
      IsOpenImmersion.lift C.opens.ι f.left (by rw [C.opens.range_ι]; exact hf))
    (by
      change IsOpenImmersion.lift C.opens.ι f.left _ ≫ C.opens.ι ≫ X.hom = W.hom
      rw [IsOpenImmersion.lift_fac_assoc, Over.w f])

@[reassoc (attr := simp)]
theorem lift_incl {W : Over (Spec (CommRingCat.of k))} (f : W ⟶ X)
    (hf : Set.range f.left ⊆ C.opens) : C.lift f hf ≫ C.incl = f :=
  Over.OverMorphism.ext (IsOpenImmersion.lift_fac C.opens.ι f.left _)

/-- The first cell factor maps onto the open cell. -/
def orbitLift : C.M.X ⟶ C.scheme :=
  C.lift (cellOrbit a x C.iM) (show Set.range _ ⊆ (C.opens : Set X.left) from fun _ hp => hp)

@[reassoc (attr := simp)]
theorem orbitLift_incl : C.orbitLift ≫ C.incl = cellOrbit a x C.iM :=
  C.lift_incl _ _

/-- The triple cell maps onto the open cell. -/
def cellLift : C.Ω ⟶ C.scheme :=
  C.lift C.cellMap (by rw [C.range_cellMap]; rfl)

@[reassoc (attr := simp)]
theorem cellLift_incl : C.cellLift ≫ C.incl = C.cellMap :=
  C.lift_incl _ _

theorem cellLift_eq : C.cellLift = fst C.M.X (C.Z.X ⊗ C.U.X) ≫ C.orbitLift := by
  rw [← cancel_mono C.incl, cellLift_incl, Category.assoc, orbitLift_incl, cellMap_eq]

theorem cellLift_left :
    C.cellLift.left = IsOpenImmersion.lift C.opens.ι C.cellMap.left
      (by rw [C.opens.range_ι, C.range_cellMap]; rfl) := rfl

instance : Flat C.cellLift.left := by
  rw [cellLift_left]
  exact MorphismProperty.of_isPullback
    (IsOpenImmersion.isPullback_lift_id C.cellMap.left C.opens.ι _).flip inferInstance

instance [QuasiCompact (Dynamic.tripleCellMultiplication C.iM C.iZ C.iU).left]
    [QuasiCompact (a.orbitMap x).left] : QuasiCompact C.cellLift.left := by
  have : QuasiCompact C.cellMap.left := by
    rw [cellMap, Over.comp_left]; infer_instance
  rw [cellLift_left]
  exact MorphismProperty.of_isPullback
    (IsOpenImmersion.isPullback_lift_id C.cellMap.left C.opens.ι _).flip inferInstance

instance : Surjective C.cellLift.left := by
  constructor
  intro y
  have hy : C.opens.ι y ∈ Set.range C.cellMap.left := by
    rw [C.range_cellMap]
    exact y.2
  obtain ⟨p, hp⟩ := hy
  refine ⟨p, C.opens.ι.isOpenEmbedding.injective ?_⟩
  rw [← hp]
  exact congrArg (fun f => f.left p) C.cellLift_incl

/-- Two points of the first factor have the same image in the cell exactly when they differ by
a stabilizing point. -/
theorem orbitLift_eq_iff {W : Over (Spec (CommRingCat.of k))} (m m' : W ⟶ C.M.X) :
    m ≫ C.orbitLift = m' ≫ C.orbitLift ↔
      a.act ((m⁻¹ * m') ≫ C.iM.hom.hom) (toUnit W ≫ x) = toUnit W ≫ x := by
  rw [← cancel_mono C.incl, Category.assoc, Category.assoc, orbitLift_incl, cellOrbit,
    ← Category.assoc, ← Category.assoc, a.comp_orbitMap, a.comp_orbitMap, MonObj.mul_comp,
    a.act_mul, GrpObj.inv_comp]
  constructor
  · intro h
    rw [← h, ← a.act_mul, inv_mul_cancel, a.act_one]
  · intro h
    calc a.act (m ≫ C.iM.hom.hom) (toUnit W ≫ x)
        = a.act (m ≫ C.iM.hom.hom) (a.act (m ≫ C.iM.hom.hom)⁻¹
            (a.act (m' ≫ C.iM.hom.hom) (toUnit W ≫ x))) := by rw [h]
      _ = a.act (m' ≫ C.iM.hom.hom) (toUnit W ≫ x) := by
            rw [← a.act_mul, ← a.act_mul, mul_inv_cancel, one_mul]

/-- **Stability of the cell.** The open cell is stable under every cocharacter whose image
centralizes `χ`. -/
theorem isGmStable (ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hψ : SubgroupFunctor.range ψ ≤ Dynamic.centralizer C.χ) :
    (a.restrict ψ).IsGmStable C.incl := by
  intro Q s z
  refine ⟨C.lift ((a.restrict ψ).act s (z ≫ C.incl)) ?_, C.lift_incl _ _⟩
  rintro _ ⟨p, rfl⟩
  obtain ⟨p', hp'⟩ := (pullback.fst z.left C.cellLift.left).surjective p
  let P : Over (Spec (CommRingCat.of k)) := Over.mk (pullback.fst z.left C.cellLift.left ≫ Q.hom)
  let φ : P ⟶ Q := Over.homMk (pullback.fst z.left C.cellLift.left) rfl
  let ω : P ⟶ C.Ω := Over.homMk (pullback.snd z.left C.cellLift.left) (by
    change pullback.snd z.left C.cellLift.left ≫ C.Ω.hom =
      pullback.fst z.left C.cellLift.left ≫ Q.hom
    rw [← Over.w C.cellLift, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w z])
  have hφω : φ ≫ z = ω ≫ C.cellLift := Over.OverMorphism.ext pullback.condition
  have hg : (φ ≫ s) ≫ ψ.hom.hom ∈ (Dynamic.centralizer C.χ).carrier P :=
    hψ P (SubgroupFunctor.mem_range.mpr ⟨φ ≫ s, rfl⟩)
  obtain ⟨m', hm'⟩ := C.exists_act_cellOrbit hg (ω ≫ fst C.M.X (C.Z.X ⊗ C.U.X))
  have key : φ ≫ (a.restrict ψ).act s (z ≫ C.incl) = m' ≫ cellOrbit a x C.iM := by
    rw [SchemeAction.restrict_act, a.naturality, ← Category.assoc φ z, hφω, Category.assoc,
      cellLift_incl, cellMap_eq, ← hm']
    simp only [Category.assoc]
  refine ⟨m'.left p', ?_⟩
  rw [← hp']
  exact (congrArg (fun f => f.left p') key).symm

/-- Points of the image of `χ` fix `x`. -/
theorem act_χ_eq {W : Over (Spec (CommRingCat.of k))} (t : W ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    a.act (t ≫ C.χ.hom.hom) (toUnit W ≫ x) = toUnit W ≫ x :=
  C.act_eq_of_mem_centralizer
    (Dynamic.range_le_centralizer C.χ W (SubgroupFunctor.mem_range.mpr ⟨t, rfl⟩))

/-- **Contraction.** Every point of the cell image of the first factor flows to `x` under the
opposite cocharacter. -/
theorem exists_limit {W : Over (Spec (CommRingCat.of k))} (m : W ⟶ C.M.X) :
    ∃ e, (a.restrict (Dynamic.oppositeCocharacter C.χ)).IsGmOrbitExtension
      (m ≫ cellOrbit a x C.iM) e ∧ Dynamic.evalZero e = toUnit W ≫ x := by
  have hm : m ≫ C.iM.hom.hom ∈
      (Dynamic.unipotent (Dynamic.oppositeCocharacter C.χ)).carrier W := by
    rw [← C.hM.2]
    exact SubgroupFunctor.mem_range.mpr ⟨m, rfl⟩
  obtain ⟨eu, heu, heu0⟩ := hm
  refine ⟨a.act eu (toUnit _ ≫ x), ?_, ?_⟩
  · have heu' : W ◁ AffineLine.unitInclusion _ ≫ eu =
        Dynamic.orbit (Dynamic.oppositeCocharacter C.χ) (m ≫ C.iM.hom.hom) := heu
    have hinv : a.act (snd W (Gm (Spec (CommRingCat.of k))).X ≫
        (Dynamic.oppositeCocharacter C.χ).hom.hom)⁻¹ (toUnit _ ≫ x) = toUnit _ ≫ x := by
      rw [Dynamic.oppositeCocharacter, Grp.comp_hom_hom, ← Category.assoc, ← GrpObj.inv_comp]
      exact C.act_χ_eq _
    rw [SchemeAction.IsGmOrbitExtension, a.naturality, heu', comp_toUnit_assoc, Dynamic.orbit,
      a.act_mul, a.act_mul, hinv, SchemeAction.gmOrbit, SchemeAction.restrict_act, cellOrbit,
      ← Category.assoc, ← Category.assoc, a.comp_orbitMap, a.naturality, comp_toUnit_assoc]
  · rw [Dynamic.evalZero, a.naturality, ← Dynamic.evalZero, heu0, a.act_one, comp_toUnit_assoc]

variable [IsSeparated X.hom] [IsAffineHom C.M.X.hom] [LocallyOfFiniteType C.M.X.hom]
  [QuasiCompact (Dynamic.tripleCellMultiplication C.iM C.iZ C.iU).left]
  [QuasiCompact (a.orbitMap x).left]

/-- **The Chevalley map of the cell.** For a unipotent first factor, the open cell maps to an
affine scheme, and points of the first factor with equal images there have equal images in the
cell. The map descends Chevalley's orbit map for the stabilizer of `x` along the triple cell. -/
theorem exists_chevalleyMap (hMu : IsUnipotent C.M) :
    ∃ (V : Over (Spec (CommRingCat.of k))) (_ : IsAffine V.left) (ρ : C.scheme ⟶ V),
      ∀ (W : Over (Spec (CommRingCat.of k))) (m m' : W ⟶ C.M.X),
        m ≫ C.orbitLift ≫ ρ = m' ≫ C.orbitLift ≫ ρ → m ≫ C.orbitLift = m' ≫ C.orbitLift := by
  obtain ⟨H, iH, hc, hstab⟩ := (a.restrict C.iM).exists_isClosedSubgroup_stabilizer x
  have hH : IsUnipotent H := unipotentClosedSubgroup k C.M H iH hc hMu
  obtain ⟨n, j, rep, hfib⟩ := Chevalley.exists_affine_vector_orbit k C.M H iH hc hH
  let r := VectorOrbit.orbitMap rep j
  have hV : IsAffine (VectorGroup.groupScheme (CommRingCat.of k) (n + 1)).X.left := by
    change IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin (n + 1)) (CommRingCat.of k))))
    infer_instance
  have hr : ∀ (W : Over (Spec (CommRingCat.of k))) (m m' : W ⟶ C.M.X),
      m ≫ C.orbitLift = m' ≫ C.orbitLift ↔ m ≫ r = m' ≫ r := by
    intro W m m'
    rw [hfib, hstab, orbitLift_eq_iff, SchemeAction.restrict_act]
  have key : ∀ {Y : Scheme.{u}} (p q : Y ⟶ C.Ω.left), p ≫ C.cellLift.left = q ≫ C.cellLift.left →
      p ≫ (fst C.M.X (C.Z.X ⊗ C.U.X) ≫ r).left = q ≫ (fst C.M.X (C.Z.X ⊗ C.U.X) ≫ r).left := by
    intro Y p q hpq
    let T : Over (Spec (CommRingCat.of k)) := Over.mk (p ≫ C.Ω.hom)
    have hq : q ≫ C.Ω.hom = p ≫ C.Ω.hom := by
      rw [← Over.w C.cellLift, ← Category.assoc, ← hpq, Category.assoc]
    let p' : T ⟶ C.Ω := Over.homMk p rfl
    let q' : T ⟶ C.Ω := Over.homMk q hq
    have h' : p' ≫ C.cellLift = q' ≫ C.cellLift := Over.OverMorphism.ext hpq
    rw [cellLift_eq, ← Category.assoc, ← Category.assoc, hr] at h'
    have h'' : p' ≫ fst C.M.X (C.Z.X ⊗ C.U.X) ≫ r = q' ≫ fst C.M.X (C.Z.X ⊗ C.U.X) ≫ r := by
      simpa only [Category.assoc] using h'
    exact congrArg (fun f => f.left) h''
  let ρl : C.scheme.left ⟶ (VectorGroup.groupScheme (CommRingCat.of k) (n + 1)).X.left :=
    EffectiveEpi.desc C.cellLift.left (fst C.M.X (C.Z.X ⊗ C.U.X) ≫ r).left key
  have hρ : C.cellLift.left ≫ ρl = (fst C.M.X (C.Z.X ⊗ C.U.X) ≫ r).left :=
    EffectiveEpi.fac _ _ _
  let ρ : C.scheme ⟶ (VectorGroup.groupScheme (CommRingCat.of k) (n + 1)).X :=
    Over.homMk ρl (by
      rw [← cancel_epi C.cellLift.left, ← Category.assoc, hρ, Over.w, Over.w])
  have hρ' : C.cellLift ≫ ρ = fst C.M.X (C.Z.X ⊗ C.U.X) ≫ r := Over.OverMorphism.ext hρ
  have horb : C.orbitLift ≫ ρ = r := by
    let s : C.M.X ⟶ C.Ω := CartesianMonoidalCategory.lift (𝟙 C.M.X)
      (CartesianMonoidalCategory.lift (1 : C.M.X ⟶ C.Z.X) (1 : C.M.X ⟶ C.U.X))
    have hs : s ≫ fst C.M.X (C.Z.X ⊗ C.U.X) = 𝟙 C.M.X := lift_fst _ _
    calc C.orbitLift ≫ ρ = (s ≫ fst C.M.X (C.Z.X ⊗ C.U.X)) ≫ C.orbitLift ≫ ρ := by
          rw [hs, Category.id_comp]
      _ = r := by
          rw [Category.assoc, ← Category.assoc (fst _ _), ← cellLift_eq, hρ',
            ← Category.assoc, hs, Category.id_comp]
  refine ⟨_, hV, ρ, fun W m m' h => ?_⟩
  rw [horb] at h
  exact (hr W m m').mpr h

theorem range_orbitLift : Set.range C.orbitLift.left = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  have hy : C.opens.ι p ∈ Set.range (cellOrbit a x C.iM).left := p.2
  obtain ⟨q, hq⟩ := hy
  refine ⟨q, C.opens.ι.isOpenEmbedding.injective ?_⟩
  rw [← hq]
  exact congrArg (fun f => f.left q) C.orbitLift_incl

variable [IsAlgClosed k]

/-- **Rational points of the cell.** Every rational point of the open cell is the image of a
rational point of the first factor. -/
theorem exists_orbitLift_eq (y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ C.scheme) :
    ∃ m : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ C.M.X, m ≫ C.orbitLift = y := by
  have : LocallyOfFiniteType (C.orbitLift.left ≫ C.scheme.hom) := by
    rw [Over.w C.orbitLift]; infer_instance
  have : LocallyOfFiniteType C.orbitLift.left :=
    locallyOfFiniteType_of_comp C.orbitLift.left C.scheme.hom
  obtain ⟨m, hm⟩ := exists_rationalPoint_lift_of_mem_range C.orbitLift.left y.left
    (by rw [C.range_orbitLift]; trivial)
  refine ⟨Over.homMk m ?_, Over.OverMorphism.ext hm⟩
  change m ≫ C.M.X.hom = 𝟙 _
  rw [← Over.w C.orbitLift, ← Category.assoc, hm]
  exact Over.w y

/-- **Injectivity of the Chevalley map on rational points.** -/
theorem exists_chevalleyMap_injective (hMu : IsUnipotent C.M) :
    ∃ (V : Over (Spec (CommRingCat.of k))) (_ : IsAffine V.left) (ρ : C.scheme ⟶ V),
      ∀ y y' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ C.scheme, y ≫ ρ = y' ≫ ρ → y = y' := by
  obtain ⟨V, hV, ρ, hρ⟩ := C.exists_chevalleyMap hMu
  refine ⟨V, hV, ρ, fun y y' h => ?_⟩
  obtain ⟨m, rfl⟩ := C.exists_orbitLift_eq y
  obtain ⟨m', rfl⟩ := C.exists_orbitLift_eq y'
  exact hρ _ m m' (by simpa only [Category.assoc] using h)

/-- A rational point of `X` in the open cell factors through it. -/
theorem exists_lift_of_mem (y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X)
    (hy : y.left (IsLocalRing.closedPoint k) ∈ C.opens) :
    ∃ y' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ C.scheme, y' ≫ C.incl = y := by
  refine ⟨C.lift y ?_, C.lift_incl _ _⟩
  rintro _ ⟨p, rfl⟩
  have hp : p = IsLocalRing.closedPoint k :=
    Subsingleton.elim (α := PrimeSpectrum k) _ _
  rw [hp]
  exact hy

omit [IsAlgClosed k] in
theorem mem_opens_x : x.left (⊥ : PrimeSpectrum k) ∈ C.opens := by
  refine ⟨(1 : pt' k ⟶ C.M.X).left (⊥ : PrimeSpectrum k), ?_⟩
  have h : (1 : pt' k ⟶ C.M.X) ≫ cellOrbit a x C.iM = x := by
    rw [cellOrbit, ← Category.assoc, a.comp_orbitMap, MonObj.one_comp, a.act_one,
      show toUnit (pt' k) = 𝟙 (pt' k) from toUnit_unique _ _, Category.id_comp]
  exact congrArg (fun f => f.left (⊥ : PrimeSpectrum k)) h

/-- **Two limits.** If the `χ`-orbit of a rational point of the open cell also flows to `x`,
the point is `x`: the Chevalley map is constant along the doubly extended orbit. -/
theorem eq_of_limit (hMu : IsUnipotent C.M) (y : pt' k ⟶ X)
    (hy : y.left (IsLocalRing.closedPoint k) ∈ C.opens)
    {e : pt' k ⊗ AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ X}
    (he : (a.restrict C.χ).IsGmOrbitExtension y e) (he0 : Dynamic.evalZero e = x) : y = x := by
  obtain ⟨V, hV, ρ, hρ⟩ := C.exists_chevalleyMap_injective hMu
  obtain ⟨y', rfl⟩ := C.exists_lift_of_mem y hy
  obtain ⟨m, rfl⟩ := C.exists_orbitLift_eq y'
  rw [Category.assoc, orbitLift_incl] at he
  obtain ⟨e₀, he₀, he₀0⟩ := C.exists_limit m
  rw [show toUnit (pt' k) = 𝟙 (pt' k) from toUnit_unique _ _, Category.id_comp] at he₀0
  have hstab : (a.restrict C.χ).IsGmStable C.incl :=
    C.isGmStable C.χ (Dynamic.range_le_centralizer C.χ)
  have hstab₀ : (a.restrict (Dynamic.oppositeCocharacter C.χ)).IsGmStable C.incl := by
    apply C.isGmStable
    intro W g hg
    obtain ⟨s, rfl⟩ := SubgroupFunctor.mem_range.mp hg
    exact Dynamic.range_le_centralizer C.χ W (SubgroupFunctor.mem_range.mpr
      ⟨s ≫ (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1))).hom.hom,
        by rw [Category.assoc, ← Grp.comp_hom_hom]; rfl⟩)
  have hxmem : x.left (⊥ : PrimeSpectrum k) ∈ C.incl.left.opensRange := by
    show x.left (⊥ : PrimeSpectrum k) ∈ Set.range C.incl.left
    rw [C.range_incl]
    exact C.mem_opens_x
  have h₀ : (Dynamic.evalZero e₀).left (⊥ : PrimeSpectrum k) ∈ C.incl.left.opensRange := by
    rw [he₀0]; exact hxmem
  have hInfMem : (Dynamic.evalZero e).left (⊥ : PrimeSpectrum k) ∈ C.incl.left.opensRange := by
    rw [he0]; exact hxmem
  let L₀ := SchemeAction.gmOrbitOpenLift _ C.incl hstab₀ he₀ h₀
  let L := SchemeAction.gmOrbitOpenLift _ C.incl hstab he hInfMem
  have hL₀ : L₀ ≫ C.incl = e₀ := SchemeAction.gmOrbitOpenLift_fac _ C.incl hstab₀ he₀ h₀
  have hL : L ≫ C.incl = e := SchemeAction.gmOrbitOpenLift_fac _ C.incl hstab he hInfMem
  have hι : ι[(Gm (Spec (CommRingCat.of k))).X] ≫ ι[(Gm (Spec (CommRingCat.of k))).X] = 𝟙 _ := by
    rw [GrpObj.inv_eq_inv, GrpObj.comp_inv, Category.comp_id, inv_inv]
  have hInf : pt' k ◁ AffineLine.unitInclusion (Spec (CommRingCat.of k)) ≫ L ≫ ρ =
      pt' k ◁ ι[(Gm (Spec (CommRingCat.of k))).X] ≫
        (pt' k ◁ AffineLine.unitInclusion (Spec (CommRingCat.of k)) ≫ L₀ ≫ ρ) := by
    have hcomp : pt' k ◁ AffineLine.unitInclusion (Spec (CommRingCat.of k)) ≫ L =
        pt' k ◁ ι[(Gm (Spec (CommRingCat.of k))).X] ≫
          pt' k ◁ AffineLine.unitInclusion (Spec (CommRingCat.of k)) ≫ L₀ := by
      rw [← cancel_mono C.incl]
      simp only [Category.assoc, hL, hL₀]
      rw [he, he₀, gmOrbit_opposite, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, hι,
        MonoidalCategory.whiskerLeft_id, Category.id_comp]
    rw [← Category.assoc, hcomp]
    simp only [Category.assoc]
  have key := TwoSidedConstancy.evalZero_eq_of_twoSided
    (pt' k ◁ AffineLine.unitInclusion (Spec (CommRingCat.of k)) ≫ L₀ ≫ ρ) (L₀ ≫ ρ) (L ≫ ρ)
    rfl (by rw [GmOrbitInversion.groupHom_powerHom_neg_one]; exact hInf)
  have hx0 : Dynamic.evalZero L₀ = (1 : pt' k ⟶ C.M.X) ≫ C.orbitLift := by
    rw [← cancel_mono C.incl, Dynamic.evalZero, Category.assoc, hL₀, ← Dynamic.evalZero, he₀0,
      Category.assoc, orbitLift_incl, cellOrbit, ← Category.assoc, a.comp_orbitMap,
      MonObj.one_comp, a.act_one, show toUnit (pt' k) = 𝟙 (pt' k) from toUnit_unique _ _,
      Category.id_comp]
  have hy1 : CartesianMonoidalCategory.lift (𝟙 (pt' k))
      (toUnit (pt' k) ≫ η[(Gm (Spec (CommRingCat.of k))).X]) ≫
        pt' k ◁ AffineLine.unitInclusion (Spec (CommRingCat.of k)) ≫ L₀ = m ≫ C.orbitLift := by
    rw [← cancel_mono C.incl]
    simp only [Category.assoc, hL₀]
    rw [he₀.eval_one, orbitLift_incl]
  have hrho : ((1 : pt' k ⟶ C.M.X) ≫ C.orbitLift) ≫ ρ = (m ≫ C.orbitLift) ≫ ρ := by
    rw [← hx0, ← hy1]
    simpa only [Dynamic.evalZero, Category.assoc] using key
  have := hρ _ _ hrho
  rw [← this, Category.assoc, orbitLift_incl, cellOrbit, ← Category.assoc, a.comp_orbitMap,
    MonObj.one_comp, a.act_one, show toUnit (pt' k) = 𝟙 (pt' k) from toUnit_unique _ _,
    Category.id_comp]

/-- A rational point of the cell fixed by the opposite cocharacter is `x`. -/
theorem eq_of_isFixed (y : pt' k ⟶ X) (hy : y.left (IsLocalRing.closedPoint k) ∈ C.opens)
    (hfix : (a.restrict (Dynamic.oppositeCocharacter C.χ)).IsFixed y) : y = x := by
  obtain ⟨y', rfl⟩ := C.exists_lift_of_mem y hy
  obtain ⟨m, rfl⟩ := C.exists_orbitLift_eq y'
  obtain ⟨e₀, he₀, he₀0⟩ := C.exists_limit m
  rw [Category.assoc, orbitLift_incl] at hfix ⊢
  rw [← evalZero_eq_of_isFixed _ hfix he₀, he₀0,
    show toUnit (pt' k) = 𝟙 (pt' k) from toUnit_unique _ _, Category.id_comp]

omit [IsAffineHom C.M.X.hom] [LocallyOfFiniteType C.M.X.hom]
  [QuasiCompact (Dynamic.tripleCellMultiplication C.iM C.iZ C.iU).left]
  [QuasiCompact (a.orbitMap x).left] [IsAlgClosed k] in
/-- **Stable lift.** If the orbit of a rational point under a cocharacter centralizing `χ`
flows into the open cell, the point lies in the open cell. -/
theorem mem_opens_of_limit (ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hψ : SubgroupFunctor.range ψ ≤ Dynamic.centralizer C.χ) (y : pt' k ⟶ X)
    {e : pt' k ⊗ AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ X}
    (he : (a.restrict ψ).IsGmOrbitExtension y e)
    (he0 : (Dynamic.evalZero e).left (⊥ : PrimeSpectrum k) ∈ C.opens) :
    y.left (IsLocalRing.closedPoint k) ∈ C.opens := by
  have h0 : (Dynamic.evalZero e).left (⊥ : PrimeSpectrum k) ∈ C.incl.left.opensRange := by
    show _ ∈ Set.range C.incl.left
    rw [C.range_incl]
    exact he0
  let L := SchemeAction.gmOrbitOpenLift _ C.incl (C.isGmStable ψ hψ) he h0
  have hL : L ≫ C.incl = e := SchemeAction.gmOrbitOpenLift_fac _ C.incl (C.isGmStable ψ hψ) he h0
  have hy := he.eval_one
  rw [← hL] at hy
  have hmem : y.left (IsLocalRing.closedPoint k) ∈ Set.range C.incl.left := by
    rw [← hy]
    exact ⟨_, rfl⟩
  rw [C.range_incl] at hmem
  exact hmem

end Cell








end RankOneFlagCell

end Langlands.GroupScheme
