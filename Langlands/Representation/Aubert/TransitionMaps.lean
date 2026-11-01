import Langlands.Representation.Parabolic.NaturalFirstAdjointness

/-!
# Actual transition maps for the Aubert diagram

The map from a coarser parabolic to a finer parabolic is pointwise projection
on actual Jacquet quotients. Both half-modulus factors cancel before the
covariance check. The maps compose on the actual induced representations.
-/

noncomputable section

namespace Langlands.Aubert.Transition

open GeneralLinear
open scoped NNReal

universe uF uV uW

section Quotients

variable {K : Type uF} [CommRing K] {n : ℕ}
  {B C D : BlockShape n} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Projection from the actual quotient for `B` to that for `C`, when the
upper radical for `B` is contained in the upper radical for `C`. -/
def quotient (ρ : Representation ℂ (GeneralLinear n K) V)
    (h : B.unipotentSubgroup K ≤ C.unipotentSubgroup K) :
    B.JacquetModule ρ →ₗ[ℂ] C.JacquetModule ρ :=
  (C.jacquetModuleEquiv ρ).symm.toLinearMap ∘ₗ
    Jacquet.lift ρ (B.unipotentSubgroup K)
      (Jacquet.mk ρ (C.unipotentSubgroup K))
      (fun u => LinearMap.ext fun v =>
        Jacquet.mk_apply_subgroup ρ (C.unipotentSubgroup K) ⟨u, h u.property⟩ v) ∘ₗ
      (B.jacquetModuleEquiv ρ).toLinearMap

@[simp]
theorem quotient_mk (ρ : Representation ℂ (GeneralLinear n K) V)
    (h : B.unipotentSubgroup K ≤ C.unipotentSubgroup K) (v : V) :
    quotient ρ h (B.jacquetMk ρ v) = C.jacquetMk ρ v := rfl

theorem quotient_surjective (ρ : Representation ℂ (GeneralLinear n K) V)
    (h : B.unipotentSubgroup K ≤ C.unipotentSubgroup K) :
    Function.Surjective (quotient ρ h) := by
  intro x
  obtain ⟨v, rfl⟩ := C.jacquetMk_surjective ρ x
  exact ⟨B.jacquetMk ρ v, quotient_mk ρ h v⟩

@[simp]
theorem quotient_refl (ρ : Representation ℂ (GeneralLinear n K) V) :
    quotient (B := B) ρ le_rfl = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := B.jacquetMk_surjective ρ x
  rfl

theorem quotient_comp (ρ : Representation ℂ (GeneralLinear n K) V)
    (hBC : B.unipotentSubgroup K ≤ C.unipotentSubgroup K)
    (hCD : C.unipotentSubgroup K ≤ D.unipotentSubgroup K) :
    quotient ρ hCD ∘ₗ quotient ρ hBC = quotient ρ (hBC.trans hCD) := by
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := B.jacquetMk_surjective ρ x
  change quotient ρ hCD (quotient ρ hBC (B.jacquetMk ρ v)) =
    quotient ρ (hBC.trans hCD) (B.jacquetMk ρ v)
  rw [quotient_mk, quotient_mk, quotient_mk]

end Quotients

section Normalized

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} {B C D : BlockShape n}
  {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The parabolic action that induces the normalized induction of normalized
Jacquet restriction. Its two modulus factors cancel. -/
abbrev inducing (B : BlockShape n) (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :=
  twist (T.parabolicHalfModulus B)
    ((T.normalizedJacquet B ρ).comp (B.leviProjection F.Carrier))

theorem inducing_mk (B : BlockShape n)
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (b : B.parabolic F.Carrier) (v : V) :
    inducing T B ρ b (B.jacquetMk ρ v) = B.jacquetMk ρ (ρ b v) :=
  (Parabolic.FirstAdjointness.jacquet_covariant T B
    (Representation.IntertwiningMap.id (T.normalizedJacquet B ρ)) b v).symm

/-- The actual normalized induction--Jacquet term. -/
abbrev term (B : BlockShape n) (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Representation ℂ (GeneralLinear n F.Carrier)
      (Induction.SmoothFunctions (B.parabolic F.Carrier) (inducing T B ρ)) :=
  T.normalizedParabolicInduced B (T.normalizedJacquet B ρ)

/-- Pointwise projection on full covariant function spaces, before restricting
to smooth vectors. -/
def fullMap (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (hP : C.parabolic F.Carrier ≤ B.parabolic F.Carrier)
    (hU : B.unipotentSubgroup F.Carrier ≤ C.unipotentSubgroup F.Carrier) :
    (Induction.equivariantAction (B.parabolic F.Carrier) (inducing T B ρ)).IntertwiningMap
      (Induction.equivariantAction (C.parabolic F.Carrier) (inducing T C ρ)) where
  toLinearMap :=
    { toFun := fun f => ⟨fun g => quotient ρ hU (f.1 g), by
        intro c g
        have hc := f.property (⟨c, hP c.property⟩ : B.parabolic F.Carrier) g
        change f.1 ((c : GeneralLinear n F.Carrier) * g) =
          inducing T B ρ (⟨c, hP c.property⟩ : B.parabolic F.Carrier) (f.1 g) at hc
        change quotient ρ hU (f.1 ((c : GeneralLinear n F.Carrier) * g)) =
          inducing T C ρ c (quotient ρ hU (f.1 g))
        rw [hc]
        obtain ⟨v, hv⟩ := B.jacquetMk_surjective ρ (f.1 g)
        rw [← hv, inducing_mk, quotient_mk, quotient_mk, inducing_mk]⟩
      map_add' := by
        intro f h
        ext g
        exact (quotient ρ hU).map_add (f.1 g) (h.1 g)
      map_smul' := by
        intro a f
        ext g
        exact (quotient ρ hU).map_smul a (f.1 g) }
  isIntertwining' g := by
    ext f x
    rfl

/-- The actual transition map, restricted to smooth vectors by equivariance. -/
def map (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (hP : C.parabolic F.Carrier ≤ B.parabolic F.Carrier)
    (hU : B.unipotentSubgroup F.Carrier ≤ C.unipotentSubgroup F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (term T B ρ).IntertwiningMap (term T C ρ) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  exact smoothMap (fullMap T ρ hP hU)

@[simp]
theorem map_eval (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (hP : C.parabolic F.Carrier ≤ B.parabolic F.Carrier)
    (hU : B.unipotentSubgroup F.Carrier ≤ C.unipotentSubgroup F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (f : Induction.SmoothFunctions (B.parabolic F.Carrier) (inducing T B ρ))
      (g : GeneralLinear n F.Carrier),
      Induction.eval _ _ (map T ρ hP hU f) g =
        quotient ρ hU (Induction.eval _ _ f g) := by
  intros
  rfl

@[simp]
theorem map_refl (B : BlockShape n)
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    map T (B := B) ρ le_rfl le_rfl = Representation.IntertwiningMap.id (term T B ρ) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  ext f g
  exact LinearMap.congr_fun (quotient_refl ρ) (Induction.eval _ _ f g)

theorem map_comp (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (hPBC : C.parabolic F.Carrier ≤ B.parabolic F.Carrier)
    (hUBC : B.unipotentSubgroup F.Carrier ≤ C.unipotentSubgroup F.Carrier)
    (hPCD : D.parabolic F.Carrier ≤ C.parabolic F.Carrier)
    (hUCD : C.unipotentSubgroup F.Carrier ≤ D.unipotentSubgroup F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (map T ρ hPCD hUCD).comp (map T ρ hPBC hUBC) =
      map T ρ (hPCD.trans hPBC) (hUBC.trans hUCD) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  ext f g
  exact LinearMap.congr_fun (quotient_comp ρ hUBC hUCD) (Induction.eval _ _ f g)

/-- The adjunction-unit map from a smooth representation to each diagram term. -/
def augmentation (B : BlockShape n)
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (hρ : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      IsSmooth ρ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ρ.IntertwiningMap (term T B ρ) :=
  Parabolic.FirstAdjointness.frobenius T B hρ
    (Representation.IntertwiningMap.id (T.normalizedJacquet B ρ))

@[simp]
theorem augmentation_eval (B : BlockShape n)
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (hρ : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      IsSmooth ρ) (v : V) (g : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval _ _ (augmentation T B ρ hρ v) g = B.jacquetMk ρ (ρ g v) := rfl

theorem map_augmentation (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (hρ : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      IsSmooth ρ)
    (hP : C.parabolic F.Carrier ≤ B.parabolic F.Carrier)
    (hU : B.unipotentSubgroup F.Carrier ≤ C.unipotentSubgroup F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (map T ρ hP hU).comp (augmentation T B ρ hρ) = augmentation T C ρ hρ := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  ext v g
  rfl

end Normalized

end Langlands.Aubert.Transition
