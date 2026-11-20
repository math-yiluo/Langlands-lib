import Langlands.Geometry.FormalGroup.AtlasRationalHeight
import Langlands.Geometry.FormalGroup.FiniteKernelComposition
import Langlands.Geometry.FormalGroup.RationalSectionGlobal

/-! # Addition of rational heights by composition of actual finite kernels -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}
variable {π : O} {q H : ℕ} {U : Opens (PrimeSpectrum R)}

namespace RationalSection

variable {f : RationalSection F M N U} {g : RationalSection F N P U}

namespace HeightPresentation

/-- Compose actual integral numerators and use the actual sum of the two scalar powers. -/
def comp (G : HeightPresentation π q g) (E : HeightPresentation π q f)
    (hM : (M.overAlgebra ((coefficientStructurePresheaf R).obj (op U))).HasPiHeight π q H) :
    HeightPresentation π q (RationalSection.comp g f) where
  exponent := G.exponent + E.exponent
  representative := G.representative.comp E.representative
  numeratorHeight := E.numeratorHeight + G.numeratorHeight
  denominatorHeight := (G.exponent + E.exponent) * H
  numerator := G.numerator.comp_of_finiteKernelComposition
    (Hom.finiteKernelCompositionStatement _ _ _) E.numerator
  denominator := hM.scalarPower_height _
  represents := by
    rw [pow_add, mul_smul, ← RationalSection.comp_smul, ← RationalSection.smul_comp,
      G.represents, E.represents, comp_ofIntegral]

/-- On a nonempty open the denominator exponent is determined by the actual scalar rank. -/
theorem denominatorHeight_eq [Nontrivial ((coefficientStructurePresheaf R).obj (op U))]
    (hq : 2 ≤ q) (E : HeightPresentation π q f)
    (hM : (M.overAlgebra ((coefficientStructurePresheaf R).obj (op U))).HasPiHeight π q H) :
    E.denominatorHeight = E.exponent * H :=
  E.denominator.unique hq (hM.scalarPower_height _)

/-- For the same finite scalar height, the signed rank differences add. -/
theorem index_comp [Nontrivial ((coefficientStructurePresheaf R).obj (op U))]
    (hq : 2 ≤ q) (G : HeightPresentation π q g) (E : HeightPresentation π q f)
    (hM : (M.overAlgebra ((coefficientStructurePresheaf R).obj (op U))).HasPiHeight π q H)
    (hN : (N.overAlgebra ((coefficientStructurePresheaf R).obj (op U))).HasPiHeight π q H) :
    (G.comp E hM).index = E.index + G.index := by
  change ((E.numeratorHeight + G.numeratorHeight : ℕ) : ℤ) -
    (((G.exponent + E.exponent) * H : ℕ) : ℤ) =
    ((E.numeratorHeight : ℤ) - E.denominatorHeight) +
      ((G.numeratorHeight : ℤ) - G.denominatorHeight)
  rw [E.denominatorHeight_eq hq hM, G.denominatorHeight_eq hq hN]
  push_cast
  ring

end HeightPresentation

namespace HasHeightFunction

/-- At each point compose the two actual presentations on their common neighbourhood. -/
theorem comp (hq : 2 ≤ q) (hM : M.HasPiHeight π q H) (hN : N.HasPiHeight π q H)
    {s t : U → ℤ} (hg : HasHeightFunction π q g t) (hf : HasHeightFunction π q f s) :
    HasHeightFunction π q (RationalSection.comp g f) (fun x => s x + t x) := by
  intro x
  obtain ⟨V, hxV, i, E, hE⟩ := hf x
  obtain ⟨W, hxW, j, G, hG⟩ := hg x
  let a : V ⊓ W ⟶ V := homOfLE inf_le_left
  let b : V ⊓ W ⟶ W := homOfLE inf_le_right
  let k : V ⊓ W ⟶ U := a ≫ i
  have hk : b ≫ j = k := Subsingleton.elim _ _
  have he : RationalSection.restrict a (RationalSection.restrict i f) =
      RationalSection.restrict k f := (restrict_comp i a f).symm
  have hg' : RationalSection.restrict b (RationalSection.restrict j g) =
      RationalSection.restrict k g := (restrict_comp j b g).symm.trans
        (congrArg (fun l => RationalSection.restrict l g) hk)
  let E' : HeightPresentation π q (RationalSection.restrict k f) := he ▸ E.restrict a
  let G' : HeightPresentation π q (RationalSection.restrict k g) := hg' ▸ G.restrict b
  let T := (coefficientStructurePresheaf R).obj (op (V ⊓ W))
  let φ : R →ₐ[O] T := IsScalarTower.toAlgHom O R T
  have hMT : (M.overAlgebra T).HasPiHeight π q H := hM.map φ
  have hNT : (N.overAlgebra T).HasPiHeight π q H := hN.map φ
  let : Nontrivial ((Spec.structureSheaf R).presheaf.stalk (x : PrimeSpectrum R)) :=
    IsLocalization.AtPrime.nontrivial _ x.val.asIdeal
  let : Nontrivial T :=
    ((Spec.structureSheaf R).presheaf.germ (V ⊓ W) (x : PrimeSpectrum R) ⟨hxV, hxW⟩).hom.domain_nontrivial
  have hc := (restrict_comp_hom k g f).symm
  refine ⟨V ⊓ W, ⟨hxV, hxW⟩, k, hc ▸ G'.comp E' hMT, ?_⟩
  intro y
  change s ⟨y, _⟩ + t ⟨y, _⟩ = _
  rw [HeightPresentation.index_cast, HeightPresentation.index_comp hq G' E' hMT hNT]
  have he' : E'.index = E.index := by simp only [E', HeightPresentation.index_cast, HeightPresentation.index_restrict]
  have hg'' : G'.index = G.index := by simp only [G', HeightPresentation.index_cast, HeightPresentation.index_restrict]
  rw [he', hg'']
  exact congrArg₂ (· + ·) (hE ⟨y, y.property.1⟩) (hG ⟨y, y.property.2⟩)

end HasHeightFunction
end RationalSection

namespace BasicAtlas.RationalHom.HasConstantChartHeight

variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {Z : BasicAtlas O R υ}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}
variable {f : BasicAtlas.RationalHom F X Y h} {g : BasicAtlas.RationalHom F Y Z k}

/-- Composition adds the actual signed heights on every test of the common cover. -/
theorem comp (hq : 2 ≤ q)
    (hX : ∀ b : X.opens, (X.chart b).HasPiHeight π q H)
    (hY : ∀ b : Y.opens, (Y.chart b).HasPiHeight π q H)
    {m n : ℤ} (hg : g.HasConstantChartHeight π q n) (hf : f.HasConstantChartHeight π q m) :
    (BasicAtlas.RationalHom.comp g f).HasConstantChartHeight π q (m + n) := by
  intro A b hb
  rw [BasicAtlas.RationalHom.onChart_comp]
  simp only [← RationalSection.ofGlobalOn_top, RationalSection.ofGlobalOn_comp]
  exact RationalSection.HasHeightFunction.comp hq
    ((hX (sourceChart h (sourceChart k b))).map (coefficientLift b.val A hb))
    ((hY (sourceChart k b)).map (coefficientLift b.val A hb))
    (hg A b hb) (hf A (sourceChart k b) hb)

end BasicAtlas.RationalHom.HasConstantChartHeight

end Langlands.FormalGroup.ModuleLaw
