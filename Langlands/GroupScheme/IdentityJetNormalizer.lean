import Langlands.AlgebraicGeometry.NoetherianIdealSheafFiniteSupport
import Langlands.GroupScheme.IdentityJetClosedSubgroupContainment
import Langlands.GroupScheme.IdentityJetSeparatedLocalBases
import Langlands.GroupScheme.IdentityJetStabilizer
import Langlands.GroupScheme.SubgroupFunctor.NormalizerBaseChange

/-! # Finite detection of normalizers by actual identity jets -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.IdentityJet

open SubgroupFunctor

variable {S : Scheme.{u}} {H G : GroupScheme S}

private theorem separated_source [IsSeparated G.X.hom] {i : H ⟶ G}
    (hi : IsClosedSubgroup i) : IsSeparated H.X.hom := by
  have : IsClosedImmersion i.hom.hom.left := hi
  rw [← i.hom.hom.w]
  infer_instance

/-- The identity jet of a smooth closed subgroup has a closed conjugation stabilizer
over an affine base. -/
theorem stabilizer_isClosedRepresentable {R : CommRingCat.{u}} {H G : GroupScheme (Spec R)}
    [IsSeparated G.X.hom] [Smooth H.X.hom] (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (n : ℕ) : (stabilizer i n).IsClosedRepresentable := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsSeparated H.X.hom := separated_source hi
  have hfinite := finite_projection H n
  have hflat := flat_projection H n
  have hfp := locallyOfFinitePresentation_projection H n
  let : IsFinite (overScheme H n).hom := hfinite
  let : Flat (overScheme H n).hom := hflat
  let : LocallyOfFinitePresentation (overScheme H n).hom := hfp
  have : IsClosedImmersion (inclusion H n) :=
    inferInstanceAs (IsClosedImmersion (ideal H n).subschemeι)
  exact closedFiniteSubschemeStabilizer R G _ (toGroup i n)
    (inferInstanceAs (IsClosedImmersion (inclusion H n ≫ i.hom.hom.left)))

private theorem range_le_of_ker_le {C D : GroupScheme S} {a : C ⟶ G} {b : D ⟶ G}
    (hb : IsClosedSubgroup b) (h : b.hom.hom.left.ker ≤ a.hom.hom.left.ker) :
    range a ≤ range b := by
  have : IsClosedImmersion b.hom.hom.left := hb
  let lift := IsClosedImmersion.lift b.hom.hom.left a.hom.hom.left h
  have hlift : lift ≫ b.hom.hom.left = a.hom.hom.left := IsClosedImmersion.lift_fac _ _ _
  let v : C.X ⟶ D.X := Over.homMk lift (by
    rw [← b.hom.hom.w, ← Category.assoc, hlift, a.hom.hom.w])
  have hv : v ≫ b.hom.hom = a.hom.hom := Over.OverMorphism.ext hlift
  intro U g hg
  obtain ⟨x, rfl⟩ := mem_range.mp hg
  exact mem_range.mpr ⟨x ≫ v, by rw [Category.assoc, hv]⟩

private theorem ker_le_of_range_le {C D : GroupScheme S} {a : C ⟶ G} {b : D ⟶ G}
    (h : range a ≤ range b) : b.hom.hom.left.ker ≤ a.hom.hom.left.ker := by
  have ha : a.hom.hom ∈ (range a).carrier C.X := mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨v, hv⟩ := mem_range.mp (h C.X ha)
  have hv' : v.left ≫ b.hom.hom.left = a.hom.hom.left :=
    congrArg (fun w : C.X ⟶ G.X => w.left) hv
  rw [← hv']
  exact v.left.le_ker_comp b.hom.hom.left

private theorem stabilizer_eventuallyConstant [IsNoetherian G.X.left] [IsSeparated G.X.hom]
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hclosed : ∀ n, (stabilizer i n).IsClosedRepresentable) :
    ∃ n : ℕ, ∀ m, n ≤ m → stabilizer i m = stabilizer i n := by
  classical
  choose C j hj hjclosed using hclosed
  let I (n : ℕ) := (j n).hom.hom.left.ker
  have hmono : Monotone I := by
    intro m n hmn
    apply ker_le_of_range_le (a := j n) (b := j m)
    rw [(hj n).2, (hj m).2]
    exact stabilizer_antitone i hi hmn
  obtain ⟨s, hs⟩ := Langlands.AlgebraicGeometry.NoetherianIdealSheaf.exists_finite_sup I
  let n := s.sup id
  refine ⟨n, fun m hnm => le_antisymm (stabilizer_antitone i hi hnm) ?_⟩
  rw [← (hj n).2, ← (hj m).2]
  apply range_le_of_ker_le (hjclosed m)
  change I m ≤ I n
  rw [← show (⨆ l, I l) = I n from le_antisymm
    (hs.trans_le (Finset.sup_le fun l hl => hmono (Finset.le_sup (f := id) hl)))
    (le_iSup I n)]
  exact le_iSup I m

private theorem range_innerIso_le_of_forall_stabilizer [IsLocallyNoetherian S]
    [IsSeparated G.X.hom] [IsSeparated H.X.hom] [Smooth H.X.hom]
    [GeometricallyConnected H.X.hom] (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (g : Over.mk (𝟙 S) ⟶ G.X) (hg : ∀ n, g ∈ (stabilizer i n).carrier _) :
    range (i ≫ (G.innerIso g).hom) ≤ range i := by
  apply identityJetClosedSubgroupContainment (i ≫ (G.innerIso g).hom) i hi
  intro n
  let a : overScheme H n ⟶ Over.mk (𝟙 S) := Over.homMk (projection H n) (Category.comp_id _)
  let x := toGroup i n
  have hx : x ∈ schemePointRange x (overScheme H n) := ⟨𝟙 _, Category.id_comp _⟩
  have hconj := ((mem_toGroup_iff i hi n _).mp ((hg n) _ a x hx).1).1
  obtain ⟨y, hy⟩ := mem_range.mp hconj
  refine ⟨y.left, ?_⟩
  have hy' : y ≫ i.hom.hom = x ≫ (G.innerIso g).hom.hom.hom := by
    rw [hy, G.comp_innerIso_hom]
    rfl
  simpa only [Over.comp_left, x, toGroup_left, Grp.comp_hom_hom, Category.assoc]
    using congrArg (fun w : overScheme H n ⟶ G.X => w.left) hy'

private theorem mem_normalizer_at_base_of_forall_stabilizer [IsLocallyNoetherian S]
    [IsSeparated G.X.hom] [IsSeparated H.X.hom] [Smooth H.X.hom]
    [GeometricallyConnected H.X.hom] (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (g : Over.mk (𝟙 S) ⟶ G.X) (hg : ∀ n, g ∈ (stabilizer i n).carrier _) :
    g ∈ (range i).normalizer.carrier _ := by
  have hf := range_innerIso_le_of_forall_stabilizer i hi g hg
  have hr := range_innerIso_le_of_forall_stabilizer i hi g⁻¹
    (fun n => ((stabilizer i n).carrier _).inv_mem (hg n))
  intro V a x hx
  have ha : a ≫ g = G.constantPoint g V := by
    congr 1
    apply Over.OverMorphism.ext
    have hw : a.left ≫ 𝟙 S = V.hom := a.w
    change a.left = V.hom
    exact (Category.comp_id a.left).symm.trans hw
  obtain ⟨y, rfl⟩ := mem_range.mp hx
  have h (k : Over.mk (𝟙 S) ⟶ G.X) :
      (y ≫ i.hom.hom) ≫ (G.innerIso k).hom.hom.hom ∈
        (range (i ≫ (G.innerIso k).hom)).carrier V :=
    mem_range.mpr ⟨y, by rw [Grp.comp_hom_hom, Category.assoc]⟩
  refine ⟨?_, ?_⟩
  · rw [ha, ← G.comp_innerIso_hom]
    exact hf V (h g)
  · have hb := hr V (h g⁻¹)
    rw [G.comp_innerIso_hom] at hb
    simpa only [GroupScheme.constantPoint, GrpObj.comp_inv, inv_inv, ha] using hb

private theorem mem_normalizer_of_forall_stabilizer
    [IsSeparated G.X.hom] [IsSeparated H.X.hom] [Smooth H.X.hom]
    [GeometricallyConnected H.X.hom] (i : H ⟶ G) (hi : IsClosedSubgroup i)
    {U : Over S} [IsLocallyNoetherian U.left] (g : U ⟶ G.X)
    (hg : ∀ n, g ∈ (stabilizer i n).carrier U) : g ∈ (range i).normalizer.carrier U := by
  let b := U.hom
  let G' := (baseChange b).obj G
  let H' := (baseChange b).obj H
  let i' : H' ⟶ G' := (baseChange b).map i
  let V := Over.mk (𝟙 U.left)
  let e : (Over.map b).obj V ≅ U :=
    Over.isoMk (Iso.refl _) (by
      change (𝟙 _) ≫ U.hom = (𝟙 _) ≫ b
      rfl)
  let eqv := baseChangePointsEquiv b G V
  let g' := eqv.symm (e.hom ≫ g)
  have : IsSeparated G'.X.hom := MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  have : IsSeparated H'.X.hom := MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  have : Smooth H'.X.hom := MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  have : GeometricallyConnected H'.X.hom :=
    MorphismProperty.pullback_snd (P := @GeometricallyConnected) _ _ inferInstance
  have hg' (n : ℕ) : g' ∈ (stabilizer i' n).carrier V := by
    change g' ∈ (stabilizer ((baseChange b).map i) n).carrier V
    rw [← stabilizer_baseChange b, mem_baseChange]
    change eqv (eqv.symm (e.hom ≫ g)) ∈ _
    rw [MulEquiv.apply_symm_apply]
    exact (stabilizer i n).comp_mem e.hom (hg n)
  have hn := mem_normalizer_at_base_of_forall_stabilizer i' (hi.baseChange b) g' hg'
  change g' ∈ (range ((baseChange b).map i)).normalizer.carrier V at hn
  rw [range_baseChangeHom, ← normalizer_baseChange, mem_baseChange] at hn
  change eqv (eqv.symm (e.hom ≫ g)) ∈ _ at hn
  rw [MulEquiv.apply_symm_apply] at hn
  simpa only [Iso.inv_hom_id_assoc] using (range i).normalizer.comp_mem e.inv hn

/-- For a smooth geometrically connected closed subgroup of a separated group locally of
finite type and quasi-compact over a noetherian affine base, the normalizer is a closed
subgroup functor and agrees with the conjugation stabilizers of all sufficiently large
identity jets. -/
def IdentityJetNormalizerStatement : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (H G : GroupScheme (Spec R))
    [IsSeparated G.X.hom] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [Smooth H.X.hom] [GeometricallyConnected H.X.hom] (i : H ⟶ G), IsClosedSubgroup i →
    (range i).normalizer.IsClosedRepresentable ∧
      ∃ n : ℕ, ∀ m : ℕ, n ≤ m → stabilizer i m = (range i).normalizer

set_option maxHeartbeats 1000000 in
theorem identityJetNormalizer : IdentityJetNormalizerStatement.{u} := by
  intro R _ H G _ _ hqc _ _ i hi
  have : IsSeparated H.X.hom := separated_source hi
  have : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have : CompactSpace G.X.left :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact) (f := G.X.hom)).mp hqc
  have : IsNoetherian G.X.left := ⟨⟩
  obtain ⟨n, hn⟩ := stabilizer_eventuallyConstant i hi (stabilizer_isClosedRepresentable i hi)
  obtain ⟨N, j, hj, hjclosed⟩ := stabilizer_isClosedRepresentable i hi n
  have hstable : stabilizer i n = (range i).normalizer := by
    apply le_antisymm _ (normalizer_le_stabilizer i hi n)
    rw [← hj.2]
    have : IsClosedImmersion j.hom.hom.left := hjclosed
    have : IsLocallyNoetherian N.X.left := LocallyOfFiniteType.isLocallyNoetherian j.hom.hom.left
    have hg : j.hom.hom ∈ (stabilizer i n).carrier N.X := by
      rw [← hj.2]
      exact mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
    have hall (m : ℕ) : j.hom.hom ∈ (stabilizer i m).carrier N.X := by
      rcases le_total n m with hnm | hmn
      · rw [hn m hnm]
        exact hg
      · exact stabilizer_antitone i hi hmn N.X hg
    have hnorm := mem_normalizer_of_forall_stabilizer i hi j.hom.hom hall
    intro U g hg
    obtain ⟨x, rfl⟩ := mem_range.mp hg
    exact (range i).normalizer.comp_mem x hnorm
  refine ⟨?_, n, fun m hnm => (hn m hnm).trans hstable⟩
  rw [← hstable]
  exact ⟨N, j, hj, hjclosed⟩

end Langlands.GroupScheme.IdentityJet
