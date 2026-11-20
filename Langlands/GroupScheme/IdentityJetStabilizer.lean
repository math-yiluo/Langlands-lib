import Langlands.GroupScheme.IdentityJetConjugationAction
import Langlands.GroupScheme.ConjugationStabilizerBaseChange
import Langlands.GroupScheme.IdentityJetSeparatedBaseChange
import Langlands.GroupScheme.InnerAutomorphism

/-! # Conjugation stabilizers of actual identity jets -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.IdentityJet

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- Actual identity jets of an actual closed subgroup are the closed pullbacks
of the corresponding jets of its ambient group. -/
private theorem map_isPullback_of_isClosedImmersion [IsSeparated G.X.hom] (f : H ⟶ G)
    [IsClosedImmersion f.hom.hom.left] (n : ℕ) :
    IsPullback (inclusion H n) (map f n) f.hom.hom.left (inclusion G n) := by
  have : IsClosedImmersion (inclusion H n) := inferInstanceAs (IsClosedImmersion (ideal H n).subschemeι)
  have : IsClosedImmersion (inclusion G n) := inferInstanceAs (IsClosedImmersion (ideal G n).subschemeι)
  have he : IsPullback H.identitySection (𝟙 S) f.hom.hom.left G.identitySection :=
    IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp, identitySection_naturality]⟩
  have hk : G.identitySection.ker.comap f.hom.hom.left = H.identitySection.ker := by
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
      ← he.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
  apply isPullback_of_isClosedImmersion _ _ _ _ (map_inclusion f n).symm
  simp only [inclusion, Scheme.IdealSheafData.ker_subschemeι, ideal, idealSheaf_comap_pow, hk]

/-- The actual identity neighborhood as a scheme over the base. -/
def overScheme (H : GroupScheme S) (n : ℕ) : Over S := Over.mk (projection H n)

/-- The order-`n` identity neighborhood of the source mapped into the target group. -/
def toGroup (i : H ⟶ G) (n : ℕ) : overScheme H n ⟶ G.X :=
  overInclusion H n ≫ i.hom.hom

@[simp]
theorem toGroup_left (i : H ⟶ G) (n : ℕ) :
    (toGroup i n).left = inclusion H n ≫ i.hom.hom.left := rfl

/-- The subgroup functor preserving an actual identity jet by conjugation. -/
def stabilizer (i : H ⟶ G) (n : ℕ) : SubgroupFunctor G :=
  conjugationStabilizer (toGroup i n)

private theorem toGroup_baseChange_comm {T : Scheme.{u}} (b : T ⟶ S)
    [IsSeparated H.X.hom] (i : H ⟶ G) (n : ℕ) :
    (toGroup ((baseChange b).map i) n).left ≫ pullback.fst G.X.hom b =
      baseChangeMap H b n ≫ (toGroup i n).left := by
  simp only [toGroup_left, Category.assoc, baseChangeMap_inclusion_assoc]
  congr 1
  exact pullback.lift_fst _ _ _

/-- The stabilizers of actual identity jets commute with arbitrary base change. -/
theorem stabilizer_baseChange {T : Scheme.{u}} (b : T ⟶ S) [IsSeparated H.X.hom]
    (i : H ⟶ G) (n : ℕ) :
    (stabilizer i n).baseChange b = stabilizer ((baseChange b).map i) n :=
  conjugationStabilizerBaseChange b _ _ (baseChangeMap H b n)
    (baseChange_isPullback H b n) (toGroup_baseChange_comm b i n)

/-- The order-`n` jet of a closed subgroup is its intersection with the ambient jet,
on the literal points of every test scheme. -/
theorem mem_toGroup_iff [IsSeparated G.X.hom] (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (n : ℕ) {U : Over S} (x : U ⟶ G.X) :
    x ∈ schemePointRange (toGroup i n) U ↔
      x ∈ (SubgroupFunctor.range i).carrier U ∧
        x ∈ schemePointRange (overInclusion G n) U := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have hp := map_isPullback_of_isClosedImmersion i n
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨SubgroupFunctor.mem_range.mpr ⟨y ≫ overInclusion H n, Category.assoc _ _ _⟩,
      ⟨Over.homMk (y.left ≫ map i n) (by
        change (y.left ≫ map i n) ≫ projection G n = U.hom
        rw [Category.assoc, map_projection]
        exact y.w), ?_⟩⟩
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.homMk_left, toGroup_left, Category.assoc,
      map_inclusion, overInclusion]
  · rintro ⟨⟨y, hy⟩, z, hz⟩
    have he : y.left ≫ i.hom.hom.left = z.left ≫ inclusion G n :=
      congrArg (fun a : U ⟶ G.X => a.left) (hy.trans hz.symm)
    let lift := hp.lift y.left z.left he
    refine ⟨Over.homMk lift ?_, ?_⟩
    · change lift ≫ inclusion H n ≫ H.X.hom = U.hom
      rw [← Category.assoc, hp.lift_fst]
      exact y.w
    · apply Over.OverMorphism.ext
      change lift ≫ inclusion H n ≫ i.hom.hom.left = x.left
      rw [← Category.assoc, hp.lift_fst]
      exact congrArg (fun a : U ⟶ G.X => a.left) hy

set_option maxHeartbeats 1000000 in
private theorem ambient_range_mono (G : GroupScheme S) {m n : ℕ} (h : m ≤ n)
    (U : Over S) : schemePointRange (overInclusion G m) U ⊆
      schemePointRange (overInclusion G n) U := by
  have : IsClosedImmersion (inclusion G n) :=
    inferInstanceAs (IsClosedImmersion (ideal G n).subschemeι)
  have hk : (inclusion G n).ker ≤ (inclusion G m).ker := by
    simp only [inclusion, Scheme.IdealSheafData.ker_subschemeι]
    intro V
    simp only [ideal, Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
    exact Ideal.pow_le_pow_right (Nat.succ_le_succ h)
  let t := IsClosedImmersion.lift (inclusion G n) (inclusion G m) hk
  have ht : t ≫ inclusion G n = inclusion G m := IsClosedImmersion.lift_fac _ _ _
  let a : overScheme G m ⟶ overScheme G n := Over.homMk t (by
    change t ≫ inclusion G n ≫ G.X.hom = inclusion G m ≫ G.X.hom
    rw [← Category.assoc, ht])
  have ha : a ≫ overInclusion G n = overInclusion G m := Over.OverMorphism.ext ht
  rintro _ ⟨y, rfl⟩
  refine ⟨y ≫ a, ?_⟩
  change (y ≫ a) ≫ overInclusion G n = y ≫ overInclusion G m
  rw [Category.assoc, ha]

private theorem ambient_range_conjugate_at_base (G : GroupScheme S) (n : ℕ)
    (g x : Over.mk (𝟙 S) ⟶ G.X)
    (hx : x ∈ schemePointRange (overInclusion G n) _) :
    g * x * g⁻¹ ∈ schemePointRange (overInclusion G n) _ := by
  have hg : G.constantPoint g (Over.mk (𝟙 S)) = g := by
    change Over.homMk (𝟙 S) _ ≫ g = g
    rw [show Over.homMk (𝟙 S) (by simp) = 𝟙 (Over.mk (𝟙 S)) from
      Over.OverMorphism.ext rfl, Category.id_comp]
  rw [← hg, ← G.comp_innerIso_hom g _ x]
  obtain ⟨y, rfl⟩ := hx
  let e : overScheme G n ⟶ overScheme G n :=
    Over.homMk (map (G.innerIso g).hom n) (map_projection _ _)
  refine ⟨y ≫ e, ?_⟩
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, e, Over.homMk_left, Category.assoc, overInclusion, map_inclusion]

/-- Conjugation by any point preserves membership in the actual ambient identity jet. -/
theorem ambient_range_conjugate (G : GroupScheme S) [IsSeparated G.X.hom] (n : ℕ)
    {U : Over S} (g x : U ⟶ G.X) (hx : x ∈ schemePointRange (overInclusion G n) U) :
    g * x * g⁻¹ ∈ schemePointRange (overInclusion G n) U := by
  let b := U.hom
  let G' := (baseChange b).obj G
  let V := Over.mk (𝟙 U.left)
  let e : (Over.map b).obj V ≅ U :=
    Over.isoMk (Iso.refl _) (by
      change (𝟙 _) ≫ U.hom = (𝟙 _) ≫ b
      rfl)
  let eqv := baseChangePointsEquiv b G V
  let g' := eqv.symm (e.hom ≫ g)
  let x' := eqv.symm (e.hom ≫ x)
  have hp := mem_schemePointRange_baseChange_iff b (overInclusion G n) (overInclusion G' n)
    (baseChangeMap G b n) (baseChange_isPullback G b n) (baseChangeMap_inclusion G b n).symm
    (U := V)
  have hx' : x' ∈ schemePointRange (overInclusion G' n) V := (hp x').mpr (by
    change eqv (eqv.symm (e.hom ≫ x)) ∈ _
    rw [MulEquiv.apply_symm_apply]
    obtain ⟨y, rfl⟩ := hx
    exact ⟨e.hom ≫ y, Category.assoc _ _ _⟩)
  have hc : e.hom ≫ (g * x * g⁻¹) ∈ schemePointRange (overInclusion G n) _ := by
    have hh := (hp _).mp (ambient_range_conjugate_at_base G' n g' x' hx')
    change eqv (g' * x' * g'⁻¹) ∈ _ at hh
    simpa only [map_mul, map_inv, g', x', MulEquiv.apply_symm_apply, MonObj.comp_mul,
      GrpObj.comp_inv] using hh
  obtain ⟨y, hy⟩ := hc
  change y ≫ overInclusion G n = e.hom ≫ (g * x * g⁻¹) at hy
  refine ⟨e.inv ≫ y, ?_⟩
  change (e.inv ≫ y) ≫ overInclusion G n = g * x * g⁻¹
  rw [Category.assoc, hy, Iso.inv_hom_id_assoc]

/-- Every point normalizing the subgroup stabilizes each identity jet. -/
theorem normalizer_le_stabilizer [IsSeparated G.X.hom] (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (n : ℕ) : (SubgroupFunctor.range i).normalizer ≤ stabilizer i n := by
  intro U g hg V a x hx
  obtain ⟨hsub, hamb⟩ := (mem_toGroup_iff i hi n x).mp hx
  have h := hg V a x hsub
  refine ⟨(mem_toGroup_iff i hi n _).mpr ⟨h.1, ambient_range_conjugate G n _ _ hamb⟩,
    (mem_toGroup_iff i hi n _).mpr ⟨h.2, ?_⟩⟩
  simpa only [inv_inv] using ambient_range_conjugate G n (a ≫ g)⁻¹ x hamb

/-- Stabilizers of identity jets of a closed subgroup decrease as the order increases. -/
theorem stabilizer_antitone [IsSeparated G.X.hom] (i : H ⟶ G) (hi : IsClosedSubgroup i) :
    Antitone (stabilizer i) := by
  intro m n h U g hg V a x hx
  obtain ⟨hsub, hamb⟩ := (mem_toGroup_iff i hi m x).mp hx
  have hn := hg V a x ((mem_toGroup_iff i hi n x).mpr ⟨hsub, ambient_range_mono G h V hamb⟩)
  refine ⟨(mem_toGroup_iff i hi m _).mpr
    ⟨((mem_toGroup_iff i hi n _).mp hn.1).1, ambient_range_conjugate G m _ _ hamb⟩,
    (mem_toGroup_iff i hi m _).mpr ⟨((mem_toGroup_iff i hi n _).mp hn.2).1, ?_⟩⟩
  simpa only [inv_inv] using ambient_range_conjugate G m (a ≫ g)⁻¹ x hamb

end Langlands.GroupScheme.IdentityJet
