import Langlands.GroupScheme.SimplyConnected.CoverPreimageCentralProduct
import Langlands.GroupScheme.CentralIsogeny.PowerLift
import Langlands.GroupScheme.CentralIsogeny.TorusCentralizerReflection
import Langlands.GroupScheme.Rational.GenericTorusCocharacter
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Torus.FiniteImage
import Langlands.GroupScheme.Dynamic.RepresentedStructure

/-! # The preimage of a split-torus centralizer is a split-torus centralizer -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CoverPreimage

variable {k : Type u} [Field k] {G D C : GroupScheme (Spec (CommRingCat.of k))}
  {Z : CommGroupScheme (Spec (CommRingCat.of k))}

local notation "𝔾ₘ" => Gm (Spec (CommRingCat.of k))

/-- Multiplication by a positive integer on `𝔾ₘ` is quasi-compact, flat and surjective. -/
theorem gm_multiplication_fpqc (n : ℕ) (hn : 0 < n) :
    QuasiCompact (multiplication (𝔾ₘ).toGrp n).hom.hom.left ∧
      Flat (multiplication (𝔾ₘ).toGrp n).hom.hom.left ∧
      Surjective (multiplication (𝔾ₘ).toGrp n).hom.hom.left := by
  have hT : IsTorus (𝔾ₘ).toGrp := isSplitTorus_gm.isTorus
  have : IsAffine (𝔾ₘ).X.left := SplittingAssembly.isAffine_of_isTorus (𝔾ₘ).toGrp hT
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  exact ⟨inferInstance, (hT.flat_and_surjective_multiplication hn').1,
    (hT.flat_and_surjective_multiplication hn').2⟩

/-- Precomposing a cocharacter with a positive power map does not change its centralizer. -/
theorem torusCentralizer_multiplication_comp (n : ℕ) (hn : 0 < n)
    {H : GroupScheme (Spec (CommRingCat.of k))} (χ : (𝔾ₘ).toGrp ⟶ H) :
    torusCentralizer (multiplication (𝔾ₘ).toGrp n ≫ χ) = torusCentralizer χ := by
  obtain ⟨h₁, h₂, h₃⟩ := gm_multiplication_fpqc (k := k) n hn
  exact torusCentralizer_comp_of_fpqc (T₁ := 𝔾ₘ) (T₂ := 𝔾ₘ) _ χ

/-- Up to a central factor and a positive power, every cocharacter of `G` comes from a
cocharacter of the cover `C`. -/
theorem exists_cover_cocharacter (d : D ⟶ G) [Mono d.hom.hom] (π : C ⟶ D)
    (hπ : IsCentralIsogeny π) {i : Z.toGrp ⟶ G} (hic : IsCentral i)
    (hm : IsCentralFppfCover (centralProduct i d hic)) (χ : (𝔾ₘ).toGrp ⟶ G) :
    ∃ Ψ : (𝔾ₘ).toGrp ⟶ C, torusCentralizer (Ψ ≫ π ≫ d) = torusCentralizer χ := by
  obtain ⟨N, hNpos, hN⟩ := hm.exponent
  have := hm.quasiCompact
  have := hm.flat
  have := hm.surjective
  obtain ⟨Φ, hΦ⟩ := CentralPowerLift.exists_comp_eq_multiplication_comp
    (π := centralProduct i d hic) χ hm.central hN
  let ΦD : (𝔾ₘ).toGrp ⟶ D := Φ ≫ snd Z.toGrp D
  obtain ⟨N', hN'pos, hN'⟩ := hπ.exists_pow_eq_one_kernel
  obtain ⟨Ψ, hΨ⟩ := hπ.exists_comp_eq_multiplication_comp ΦD hN'
  refine ⟨Ψ, ?_⟩
  have e1 : Ψ ≫ π ≫ d = multiplication (𝔾ₘ).toGrp (2 * N' : ℕ) ≫ ΦD ≫ d := by
    rw [← Category.assoc, hΨ, Category.assoc]
  have hpos' : 0 < 2 * N' := by omega
  have hpos : 0 < 2 * N := by omega
  rw [e1, torusCentralizer_multiplication_comp _ hpos']
  have hcen : ∀ (V : Over (Spec (CommRingCat.of k))) (t : V ⟶ (𝔾ₘ).X),
      t ≫ (Φ.hom.hom ≫ fst Z.X D.X ≫ i.hom.hom)⁻¹ ∈ (center G).carrier V := by
    intro V t
    rw [GrpObj.comp_inv, ← Category.assoc, ← Category.assoc]
    exact inv_mem (hic V _)
  have hmul : (ΦD ≫ d).hom.hom =
      (Φ.hom.hom ≫ fst Z.X D.X ≫ i.hom.hom)⁻¹ * (Φ ≫ centralProduct i d hic).hom.hom := by
    rw [Grp.comp_hom_hom Φ, comp_centralProduct, inv_mul_cancel_left]
    simp only [ΦD, Grp.comp_hom_hom, Grp.snd_hom_hom, Category.assoc]
  rw [torusCentralizer_eq_of_hom_eq_mul_central _ _ _ hcen hmul, hΦ,
    torusCentralizer_multiplication_comp _ hpos]

/-- The inverse image of the centralizer of a split subtorus of `G` under `C ⟶ D ⟶ G` is the
centralizer of a split subtorus of `C`. -/
theorem exists_splitSubtorus_torusCentralizer_eq_comap
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [IsAffineHom C.X.hom]
    [LocallyOfFiniteType C.X.hom]
    (d : D ⟶ G) [Mono d.hom.hom] (π : C ⟶ D) (hπ : IsCentralIsogeny π)
    {i : Z.toGrp ⟶ G} (hic : IsCentral i) (hm : IsCentralFppfCover (centralProduct i d hic))
    {A : CommGroupScheme (Spec (CommRingCat.of k))} (a : A.toGrp ⟶ G) (ha : IsSplitSubtorus a) :
    ∃ (A' : CommGroupScheme (Spec (CommRingCat.of k))) (a' : A'.toGrp ⟶ C),
      IsSplitSubtorus a' ∧ torusCentralizer a' = (torusCentralizer a).comap (π ≫ d) := by
  let χ : (𝔾ₘ).toGrp ⟶ G := CommGroupScheme.groupHom (centralizingCocharacter ha.1 a) ≫ a
  have hχ : torusCentralizer χ = torusCentralizer a := by
    rw [torusCentralizer_gm_eq_dynamicCentralizer]
    exact centralizingCocharacter_spec ha.1 a
  obtain ⟨Ψ, hΨ⟩ := exists_cover_cocharacter d π hπ hic hm χ
  have hT : IsTorus (𝔾ₘ).toGrp := isSplitTorus_gm.isTorus
  have : IsAffine (𝔾ₘ).X.left := SplittingAssembly.isAffine_of_isTorus (𝔾ₘ).toGrp hT
  have : IsAffineHom (𝔾ₘ).X.hom := inferInstance
  have : Smooth (𝔾ₘ).X.hom := hT.smooth
  have : ConnectedSpace (𝔾ₘ).X.left := hT.connectedSpace
  have : GeometricallyIntegral (𝔾ₘ).X.hom :=
    smoothConnectedAffineGeometry.1 k (𝔾ₘ).toGrp inferInstance inferInstance inferInstance
  have : QuasiCompact Ψ.hom.hom.left := inferInstance
  have hA' := hT.isTorus_schematicImage Ψ
  let A' : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { SchematicImage.image Ψ with comm := hA'.isCommMonObj }
  let a' : A'.toGrp ⟶ C := SchematicImage.inclusion Ψ
  let q : (𝔾ₘ).toGrp ⟶ A'.toGrp := SchematicImage.projection Ψ
  have hq : q ≫ a' = Ψ := SchematicImage.projection_inclusion Ψ
  have : Flat q.hom.hom.left := HomImage.flat_projection Ψ
  have : Surjective q.hom.hom.left := HomImage.surjective_projection Ψ
  have : QuasiCompact q.hom.hom.left := inferInstance
  refine ⟨A', a', ⟨isSplitTorus_gm.isSplitTorus_schematicImage Ψ,
    inferInstanceAs (IsClosedImmersion (SchematicImage.inclusion Ψ).hom.hom.left)⟩, ?_⟩
  rw [← torusCentralizer_comp_of_fpqc (T₁ := 𝔾ₘ) (T₂ := A') q a', hq,
    ← hπ.torusCentralizer_comap hT Ψ, ← torusCentralizer_comp_comap_of_mono (Ψ ≫ π) d,
    ← SubgroupFunctor.comap_comp, Category.assoc, hΨ, hχ]

end Langlands.GroupScheme.CoverPreimage
