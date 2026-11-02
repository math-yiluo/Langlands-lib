import Langlands.Cohomology.AbelianSheafCechH1

/-! # Coefficient naturality of the actual Čech-to-H¹ comparison -/

noncomputable section

universe w u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Langlands.Cohomology.AbelianSheafH1Naturality

open Cech AbelianSheafCechH1

section Coefficients

variable {T : TopCat.{u}} {P Q R : TopCat.Presheaf AddCommGrpCat.{u} T}
  {ι : Type w} (U : ι → Opens T)

/-- The coefficient map on ordered Čech one-cocycles. -/
def mapCocycles (φ : P ⟶ Q) : cocycles P U →+ cocycles Q U where
  toFun z := ⟨map U φ 1 z.1, by
    change d Q U 1 (map U φ 1 z.1) = 0
    rw [d_map, show d P U 1 z.1 = 0 from z.2, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- The induced coefficient homomorphism on the quotient by Čech coboundaries. -/
def mapHom (φ : P ⟶ Q) : CechH1 P U →+ CechH1 Q U :=
  QuotientAddGroup.map _ _ (mapCocycles U φ) (by
    rintro z ⟨a, rfl⟩
    exact ⟨map U φ 0 a, Subtype.ext (d_map U φ 0 a)⟩)

lemma mapHom_mk (φ : P ⟶ Q) (z : cocycles P U) :
    mapHom U φ (QuotientAddGroup.mk z) =
      QuotientAddGroup.mk (mapCocycles U φ z) := rfl

@[simp]
lemma mapHom_id (x : CechH1 P U) : mapHom U (𝟙 P) x = x := by
  induction x using QuotientAddGroup.induction_on with
  | H z => rfl

lemma mapHom_comp (φ : P ⟶ Q) (ψ : Q ⟶ R) (x : CechH1 P U) :
    mapHom U (φ ≫ ψ) x = mapHom U ψ (mapHom U φ x) := by
  induction x using QuotientAddGroup.induction_on with
  | H z => rfl

end Coefficients

section Representatives

variable {T : TopCat.{u}} {ι : Type w} {U : ι → Opens T}
  {S S' : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)}

/-- Map a primitive and its quotient section along a morphism of short complexes. -/
def mapRepresentative (φ : S ⟶ S') {z : C S.X₁.1 U 1}
    (r : Representative (S := S) z) :
    Representative (S := S') (map U φ.τ₁.hom 1 z) where
  primitive := map U φ.τ₂.hom 0 r.primitive
  quotientSection := φ.τ₃.hom.app _ r.quotientSection
  primitive_d := by
    rw [d_map, r.primitive_d]
    funext σ
    exact (congrArg (fun f : S.X₁ ⟶ S'.X₂ => f.hom.app _ (z σ)) φ.comm₁₂).symm
  quotient := by
    calc
      map U S'.g.hom 0 (map U φ.τ₂.hom 0 r.primitive) =
          map U φ.τ₃.hom 0 (map U S.g.hom 0 r.primitive) := by
        funext σ
        exact congrArg (fun f : S.X₂ ⟶ S'.X₃ => f.hom.app _ (r.primitive σ))
          φ.comm₂₃
      _ = globalCochain S'.X₃.1 U (φ.τ₃.hom.app _ r.quotientSection) := by
        rw [r.quotient, map_globalCochain]

set_option backward.isDefEq.respectTransparency false in
/-- The value of the mapped representative is the actual cohomological image. -/
lemma mapRepresentative_value (hS : S.ShortExact) (hS' : S'.ShortExact)
    (φ : S ⟶ S') {z : C S.X₁.1 U 1} (r : Representative (S := S) z) :
    (mapRepresentative φ r).value hS' = Sheaf.H.map φ.τ₁ 1 (r.value hS) := by
  dsimp [Representative.value, mapRepresentative]
  rw [← Sheaf.H.equiv₀_symm_naturality]
  exact Sheaf.H.δ_naturality 0 1 rfl hS hS' φ _

set_option backward.isDefEq.respectTransparency false in
/-- A morphism of short exact sequences with flasque middle terms commutes with comparison. -/
theorem quotientClassHom_naturality [Finite ι]
    [TopCat.Presheaf.IsFlasque S.X₂.1] [TopCat.Presheaf.IsFlasque S'.X₂.1]
    (hS : S.ShortExact) (hS' : S'.ShortExact) (φ : S ⟶ S')
    (hcov : ⊤ ≤ iSup U) (x : CechH1 S.X₁.1 U) :
    quotientClassHom hS' hcov (mapHom U φ.τ₁.hom x) =
      Sheaf.H.map φ.τ₁ 1 (quotientClassHom hS hcov x) := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    rw [mapHom_mk, quotientClassHom_mk, quotientClassHom_mk]
    let r := chosenRepresentative (S := S) hcov z
    rw [cocycleClassHom_eq_value hS' hcov _ (mapRepresentative φ r),
      mapRepresentative_value, cocycleClassHom_eq_value hS hcov z r]

end Representatives

section Comparison

variable {T : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrpCat.{u} T}

/-- Extend a coefficient morphism to the chosen injective embeddings and their cokernels. -/
def injectiveScMap (φ : F ⟶ G) :
    AbelianSheafFlasque.injectiveSc F ⟶ AbelianSheafFlasque.injectiveSc G := by
  let ψ := Injective.factorThru (φ ≫ Injective.ι G) (Injective.ι F)
  have hψ : Injective.ι F ≫ ψ = φ ≫ Injective.ι G :=
    Injective.comp_factorThru _ _
  exact
    { τ₁ := φ
      τ₂ := ψ
      τ₃ := cokernel.map (Injective.ι F) (Injective.ι G) φ ψ hψ
      comm₁₂ := hψ.symm
      comm₂₃ := (cokernel.π_desc _ _ _).symm }

@[simp]
lemma injectiveScMap_τ₁ (φ : F ⟶ G) : (injectiveScMap φ).τ₁ = φ := rfl

variable {ι : Type w} [Finite ι] (U : ι → Opens T)

set_option backward.isDefEq.respectTransparency false in
/-- The finite-cover comparison with actual H¹ is natural in the coefficient sheaf. -/
theorem comparisonHom_naturality (φ : F ⟶ G) (hcov : ⊤ ≤ iSup U)
    (x : CechH1 F.1 U) :
    comparisonHom G U hcov (mapHom U φ.hom x) =
      Sheaf.H.map φ 1 (comparisonHom F U hcov x) := by
  let : TopCat.Sheaf.IsFlasque (Injective.under F) :=
    AbelianSheafFlasque.isFlasque_of_injective (Injective.under F)
  let : TopCat.Sheaf.IsFlasque (Injective.under G) :=
    AbelianSheafFlasque.isFlasque_of_injective (Injective.under G)
  exact quotientClassHom_naturality
    (AbelianSheafFlasque.injectiveSc_shortExact F)
    (AbelianSheafFlasque.injectiveSc_shortExact G) (injectiveScMap φ) hcov x

end Comparison

end Langlands.Cohomology.AbelianSheafH1Naturality
