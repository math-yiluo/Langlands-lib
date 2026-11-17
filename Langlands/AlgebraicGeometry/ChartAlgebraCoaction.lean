import Langlands.AlgebraicGeometry.ChartAlgebraTransport
import Langlands.AlgebraicGeometry.FaithfullyFlatAlgebraDescent

/-! # Constructing a coaction from functorial chart transitions -/

noncomputable section
universe u
open CategoryTheory ModuleCat
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.ChartAlgebraDescent

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C]

namespace Datum
variable (D : Datum A B C)

/-- Compatibility of a ring-valued point with its chart. -/
def Compatible (T : CommAlgCat.{u} (CommRingCat.of A))
    (f : B →ₐ[A] T) (g : C →+* T) : Prop := ∀ b, g (algebraMap B C b) = f b

/-- A compatible ring point with its actual chart scalar structure. -/
def pointOfCompatible (T : CommAlgCat.{u} (CommRingCat.of A))
    (f : B →ₐ[A] T) (g : C →+* T) (hg : Compatible T f g) : Point (C := C) T f := by
  letI := f.toRingHom.toAlgebra
  exact { g with commutes' := hg }

/-- Point transport retaining the underlying ring homomorphism explicitly. -/
def transportHom (T : CommAlgCat.{u} (CommRingCat.of A)) (f₁ f₂ : B →ₐ[A] T)
    (g : C →+* T) (hg : Compatible T f₂ g) : C →+* T := by
  letI := f₁.toRingHom.toAlgebra
  exact (D.transport T f₁ f₂ (pointOfCompatible T f₂ g hg)).toRingHom

/-- Transported ring points have the new chart compatibility. -/
theorem transportHom_compatible (T : CommAlgCat.{u} (CommRingCat.of A))
    (f₁ f₂ : B →ₐ[A] T) (g : C →+* T) (hg : Compatible T f₂ g) :
    Compatible T f₁ (D.transportHom T f₁ f₂ g hg) := by
  let := f₁.toRingHom.toAlgebra
  exact (D.transport T f₁ f₂ (pointOfCompatible T f₂ g hg)).commutes

/-- Underlying point transport is insensitive to presentations of compatible data. -/
theorem transportHom_congr {T : CommAlgCat.{u} (CommRingCat.of A)}
    {f₁ f₂ f₁' f₂' : B →ₐ[A] T} {g g' : C →+* T}
    (h₁ : f₁ = f₁') (h₂ : f₂ = f₂') (h : g = g')
    (hg : Compatible T f₂ g) (hg' : Compatible T f₂' g') :
    D.transportHom T f₁ f₂ g hg = D.transportHom T f₁' f₂' g' hg' := by
  cases h₁
  cases h₂
  cases h
  rfl

@[simp] theorem transportHom_self (T : CommAlgCat.{u} (CommRingCat.of A))
    (f : B →ₐ[A] T) (g : C →+* T) (hg : Compatible T f g) :
    D.transportHom T f f g hg = g := by
  ext c
  exact congrArg (fun p => p c) (D.transport_self T f (pointOfCompatible T f g hg))

/-- Cocycle for underlying compatible ring-point transport. -/
theorem transportHom_trans (T : CommAlgCat.{u} (CommRingCat.of A))
    (f₁ f₂ f₃ : B →ₐ[A] T) (g : C →+* T) (hg : Compatible T f₃ g) :
    D.transportHom T f₁ f₂ (D.transportHom T f₂ f₃ g hg)
      (D.transportHom_compatible T f₂ f₃ g hg) = D.transportHom T f₁ f₃ g hg := by
  ext c
  exact congrArg (fun p => p c) (D.transport_trans T f₁ f₂ f₃ (pointOfCompatible T f₃ g hg))

/-- Coefficient naturality for the underlying compatible ring-point transport. -/
theorem transportHom_naturality {T T' : CommAlgCat.{u} (CommRingCat.of A)}
    (χ : T ⟶ T') (f₁ f₂ : B →ₐ[A] T) (g : C →+* T) (hg : Compatible T f₂ g) :
    χ.hom.toRingHom.comp (D.transportHom T f₁ f₂ g hg) =
      D.transportHom T' (χ.hom.comp f₁) (χ.hom.comp f₂) (χ.hom.toRingHom.comp g)
        (fun b => by change χ.hom (g (algebraMap B C b)) = χ.hom (f₂ b); rw [hg b]) := by
  ext c
  exact congrArg (fun p => p c)
    (D.transport_naturality χ f₁ f₂ (pointOfCompatible T f₂ g hg))

end Datum

variable [Algebra A C] [IsScalarTower A B C]

/-- The universal coefficient algebra carrying a chart and a chart-algebra point. -/
abbrev universal : CommAlgCat.{u} (CommRingCat.of A) := CommAlgCat.of A (B ⊗[A] C)

/-- The free chart in the universal coefficient algebra. -/
def leftChart : B →ₐ[A] universal (A := A) (B := B) (C := C) :=
  IsScalarTower.toAlgHom A B (B ⊗[A] C)

/-- The chart induced by the original algebra point. -/
def rightChart : B →ₐ[A] universal (A := A) (B := B) (C := C) :=
  Algebra.TensorProduct.includeRight.comp (IsScalarTower.toAlgHom A B C)

namespace Datum
variable (D : Datum A B C)

/-- Universal point transport gives the actual algebra coaction map. -/
def coactionMap : C →ₐ[B] B ⊗[A] C :=
  { D.transportHom universal leftChart rightChart Algebra.TensorProduct.includeRight.toRingHom
      (fun _ => rfl) with
    commutes' := D.transportHom_compatible universal leftChart rightChart
      Algebra.TensorProduct.includeRight.toRingHom (fun _ => rfl) }

/-- The counit multiplication on the universal coefficient algebra. -/
def counitMap : B ⊗[A] C →ₐ[B] C :=
  AlgHom.liftEquiv A B C C (AlgHom.id A C)

@[simp] theorem counitMap_tmul (b : B) (c : C) :
    counitMap (A := A) (B := B) (C := C) (b ⊗ₜ[A] c) = algebraMap B C b * c := by
  change b • c = algebraMap B C b * c
  exact Algebra.smul_def b c

/-- The two universal charts agree after counit multiplication. -/
theorem counitMap_charts :
    ((counitMap (A := A) (B := B) (C := C)).restrictScalars A).comp leftChart =
      ((counitMap (A := A) (B := B) (C := C)).restrictScalars A).comp rightChart := by
  ext b
  change counitMap ((b : B) ⊗ₜ[A] (1 : C)) = counitMap ((1 : B) ⊗ₜ[A] algebraMap B C b)
  simp

/-- Identity and coefficient naturality give the pointwise counit law. -/
theorem coactionMap_counit (c : C) :
    counitMap (A := A) (B := B) (C := C) (D.coactionMap c) = c := by
  let χ : universal (A := A) (B := B) (C := C) ⟶ CommAlgCat.of A C :=
    CommAlgCat.ofHom ((counitMap (A := A) (B := B) (C := C)).restrictScalars A)
  have hn := D.transportHom_naturality χ leftChart rightChart
    Algebra.TensorProduct.includeRight.toRingHom (fun _ => rfl)
  have hf : χ.hom.comp leftChart = χ.hom.comp rightChart := counitMap_charts
  have hg : Compatible (CommAlgCat.of A C) (χ.hom.comp rightChart)
      (χ.hom.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) := fun _ => rfl
  have hc := D.transportHom_congr (f₂ := χ.hom.comp rightChart)
    (g := χ.hom.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
    hf rfl rfl hg hg
  have hself := D.transportHom_self (CommAlgCat.of A C) (χ.hom.comp rightChart)
    (χ.hom.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) hg
  have he := congrArg (fun f : C →+* C => f c) (hn.trans (hc.trans hself))
  change counitMap (D.coactionMap c) = counitMap ((1 : B) ⊗ₜ[A] c) at he
  simpa only [counitMap_tmul, map_one, one_mul] using he

/-- The comultiplication inserts a trivial inner coefficient. -/
def comultMap : B ⊗[A] C →ₐ[B] B ⊗[A] (B ⊗[A] C) :=
  Algebra.TensorProduct.map (AlgHom.id B B) Algebra.TensorProduct.includeRight

/-- Apply the universal coaction to the right tensor factor. -/
def coactionTensorMap : B ⊗[A] C →ₐ[B] B ⊗[A] (B ⊗[A] C) :=
  Algebra.TensorProduct.map (AlgHom.id B B) (D.coactionMap.restrictScalars A)

/-- The pointwise coassociativity law follows from the chart transport cocycle. -/
theorem coactionMap_coassoc (c : C) :
    comultMap (A := A) (B := B) (C := C) (D.coactionMap c) =
      D.coactionTensorMap (D.coactionMap c) := by
  let U : CommAlgCat (CommRingCat.of A) := universal (A := A) (B := B) (C := C)
  let V : CommAlgCat (CommRingCat.of A) := CommAlgCat.of A (B ⊗[A] (B ⊗[A] C))
  let δ : U ⟶ V := CommAlgCat.ofHom ((comultMap (A := A) (B := B) (C := C)).restrictScalars A)
  let ψ : U ⟶ V := CommAlgCat.ofHom (D.coactionTensorMap.restrictScalars A)
  let ι : U ⟶ V := CommAlgCat.ofHom Algebra.TensorProduct.includeRight
  let g : C →+* U := Algebra.TensorProduct.includeRight.toRingHom
  have hg : Compatible U rightChart g := fun _ => rfl
  let L : B →ₐ[A] V := δ.hom.comp leftChart
  let M : B →ₐ[A] V := ι.hom.comp leftChart
  let R : B →ₐ[A] V := ι.hom.comp rightChart
  let gR : C →+* V := ι.hom.toRingHom.comp g
  have hgR : Compatible V R gR := fun _ => rfl
  let gM := D.transportHom V M R gR hgR
  have hgM : Compatible V M gM := D.transportHom_compatible V M R gR hgR
  have hnδ := D.transportHom_naturality δ leftChart rightChart g hg
  have hnψ := D.transportHom_naturality ψ leftChart rightChart g hg
  have hnι := D.transportHom_naturality ι leftChart rightChart g hg
  have hδr : δ.hom.comp rightChart = R := by
    ext b
    rfl
  have hψl : ψ.hom.comp leftChart = L := by
    ext b
    change (b : B) ⊗ₜ[A] D.coactionMap (1 : C) = b ⊗ₜ[A] ((1 : B) ⊗ₜ[A] (1 : C))
    rw [map_one]
    rfl
  have hψr : ψ.hom.comp rightChart = M := by
    ext b
    change (1 : B) ⊗ₜ[A] D.coactionMap (algebraMap B C b) =
      (1 : B) ⊗ₜ[A] ((b : B) ⊗ₜ[A] (1 : C))
    rw [D.coactionMap.commutes]
    rfl
  have hδg : δ.hom.toRingHom.comp g = gR := by
    ext x
    rfl
  have hψg : ψ.hom.toRingHom.comp g = ι.hom.toRingHom.comp D.coactionMap.toRingHom := by
    ext x
    rfl
  have hδ := D.transportHom_congr (T := V) (f₁ := δ.hom.comp leftChart)
    (f₂ := δ.hom.comp rightChart) (f₁' := L) (f₂' := R)
    (g := δ.hom.toRingHom.comp g) (g' := gR) rfl hδr hδg
    (fun _ => rfl) hgR
  have hψ := D.transportHom_congr (T := V) (f₁ := ψ.hom.comp leftChart)
    (f₂ := ψ.hom.comp rightChart) (f₁' := L) (f₂' := M)
    (g := ψ.hom.toRingHom.comp g) (g' := gM) hψl hψr (hψg.trans hnι)
    (fun _ => rfl) hgM
  have h1 := hnδ.trans hδ
  have h2 := hnψ.trans hψ
  have ht := D.transportHom_trans V L M R gR hgR
  exact congrArg (fun f : C →+* V => f c) (h1.trans (ht.symm.trans h2.symm))

omit [Algebra A C] [IsScalarTower A B C] in
/-- A functorial chart-transition datum canonically gives a multiplicative
coaction for faithfully flat algebra descent. No flatness is needed to form it. -/
def coaction : FaithfullyFlatAlgebraDescent.Coaction (algebraMap A B) (algebraMap B C) := by
  let φ := algebraMap A B
  let F := algebraMap B C
  have hφ : φ.toAlgebra = (inferInstance : Algebra A B) := toAlgebra_algebraMap
  have hF : F.toAlgebra = (inferInstance : Algebra B C) := toAlgebra_algebraMap
  letI : Algebra A B := φ.toAlgebra
  letI : Algebra B C := F.toAlgebra
  letI : Algebra A C := (F.comp φ).toAlgebra
  letI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let D' : Datum A B C := by
    change @Datum A B C _ _ _ φ.toAlgebra F.toAlgebra
    rw [hφ, hF]
    exact D
  have hμ : ∀ x : B ⊗[A] C,
      ((FaithfullyFlatCoalgebraDescent.descentComonad φ).ε.app (ModuleCat.of B C)).hom x =
        counitMap (A := A) (B := B) (C := C) x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul b c => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hδ : ∀ x : B ⊗[A] C,
      ((FaithfullyFlatCoalgebraDescent.descentComonad φ).δ.app (ModuleCat.of B C)).hom x =
        comultMap (A := A) (B := B) (C := C) x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul b c => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hmap : ∀ x : B ⊗[A] C,
      ((FaithfullyFlatCoalgebraDescent.descentComonad φ).map
        (ModuleCat.ofHom D'.coactionMap.toLinearMap)).hom x = D'.coactionTensorMap x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul b c => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  exact {
    map := D'.coactionMap
    counit := by
      ext c
      change ((FaithfullyFlatCoalgebraDescent.descentComonad φ).ε.app
        (ModuleCat.of B C)).hom (D'.coactionMap c) = c
      rw [hμ]
      exact D'.coactionMap_counit c
    coassoc := by
      ext c
      change ((FaithfullyFlatCoalgebraDescent.descentComonad φ).δ.app
        (ModuleCat.of B C)).hom (D'.coactionMap c) =
        ((FaithfullyFlatCoalgebraDescent.descentComonad φ).map
          (ModuleCat.ofHom D'.coactionMap.toLinearMap)).hom (D'.coactionMap c)
      rw [hδ, hmap]
      exact D'.coactionMap_coassoc c }

end Datum

omit [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] in
/-- With the displayed ring-map scalar structures, the packaged coaction has
exactly the universal point-transport map. -/
theorem Datum.coaction_map_apply (φ : A →+* B) (F : B →+* C) :
    letI := φ.toAlgebra
    letI := F.toAlgebra
    letI := (F.comp φ).toAlgebra
    letI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    ∀ (D : Datum A B C) (c : C), D.coaction.map c = D.coactionMap c := by
  intro D c
  rfl

end Langlands.AlgebraicGeometry.ChartAlgebraDescent
