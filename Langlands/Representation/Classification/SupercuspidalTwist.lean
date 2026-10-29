import Langlands.Group.GL.NormalizedCharacter
import Langlands.Representation.Category.Twist
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Twist.RealPower

/-!
# Supercuspidality under twists by characters of the determinant

A character trivial on the determinant kernel is trivial on every conjugate
block unipotent radical, so twisting leaves each actual Jacquet quotient
unchanged. Supercuspidal objects and classes are therefore closed under such
twists, including the normalized real powers `|det|^s`.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uR uG uV uF

namespace Jacquet

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V]

/-- A character trivial on `N` does not change the restricted action of `N`. -/
theorem twist_comp_subtype (χ : G →* Rˣ) (ρ : Representation R G V) {N : Subgroup G}
    (hN : N ≤ χ.ker) : (twist χ ρ).comp N.subtype = ρ.comp N.subtype := by
  ext x v
  have hx : χ x = 1 := hN x.property
  change ((χ x : R) • ρ x) v = ρ x v
  rw [hx, Units.val_one, one_smul]

/-- Twisting by a character trivial on `N` leaves the coinvariant quotient unchanged. -/
theorem subsingleton_coinvariants_twist_iff (χ : G →* Rˣ) (ρ : Representation R G V)
    {N : Subgroup G} (hN : N ≤ χ.ker) :
    Subsingleton (Coinvariants (twist χ ρ) N) ↔ Subsingleton (Coinvariants ρ N) := by
  unfold Coinvariants
  rw [twist_comp_subtype χ ρ hN]

end Jacquet

namespace GeneralLinear

section Ring

variable {R : Type uR} [CommRing R] {n : ℕ}

/-- Matrices in a standard block unipotent radical have determinant one. -/
theorem BlockShape.determinant_eq_one_of_mem_unipotentSubgroup (B : BlockShape n)
    {g : GeneralLinear n R} (hg : g ∈ B.unipotentSubgroup R) : determinant g = 1 := by
  obtain ⟨hp, hd⟩ := (B.mem_unipotentSubgroup_iff R g).mp hg
  let M : Matrix B.Index B.Index R :=
    (g : Matrix (Fin n) (Fin n) R).submatrix B.indexEquiv B.indexEquiv
  have hM : M.BlockTriangular Sigma.fst := hp
  have hentry : ∀ (i : Fin B.length) (a b : Fin (B.size i)),
      M ⟨i, a⟩ ⟨i, b⟩ = if a = b then 1 else 0 := hd
  have hblock : ∀ k, M.toSquareBlock Sigma.fst k = 1 := by
    intro k
    ext ⟨⟨i, a⟩, hi⟩ ⟨⟨j, b⟩, hj⟩
    dsimp only at hi hj
    subst hi
    subst hj
    simp [Matrix.toSquareBlock_def, Matrix.one_apply, hentry]
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
    ← Matrix.det_submatrix_equiv_self B.indexEquiv, hM.det_fintype]
  simp [hblock]

theorem BlockShape.unipotentSubgroup_le_ker_determinant (B : BlockShape n) :
    B.unipotentSubgroup R ≤ (determinant : GeneralLinear n R →* Rˣ).ker :=
  fun _ hg => B.determinant_eq_one_of_mem_unipotentSubgroup hg

/-- A character of the determinant factors through it. -/
theorem ker_determinant_le_ker_comp {S : Type uG} [Group S] (ψ : Rˣ →* S) :
    (determinant : GeneralLinear n R →* Rˣ).ker ≤ (ψ.comp determinant).ker := by
  intro g hg
  change ψ (determinant g) = 1
  rw [(determinant : GeneralLinear n R →* Rˣ).mem_ker.mp hg, map_one]

end Ring

variable {F : Type uF} [Field F] {n : ℕ}

/-- Every conjugate of a standard block unipotent radical lies in the determinant kernel. -/
theorem BlockShape.conjugateUnipotent_le_ker_determinant (B : BlockShape n)
    (g : GeneralLinear n F) :
    B.conjugateUnipotent g ≤ (determinant : GeneralLinear n F →* Fˣ).ker := by
  rintro _ ⟨u, hu, rfl⟩
  change determinant (g * u * g⁻¹) = 1
  rw [map_mul, map_mul, B.determinant_eq_one_of_mem_unipotentSubgroup hu, mul_one,
    map_inv, mul_inv_cancel]

theorem ker_determinant_le_ker_one :
    (determinant : GeneralLinear n F →* Fˣ).ker ≤ (1 : GeneralLinear n F →* ℂˣ).ker := by
  rw [MonoidHom.ker_one]
  exact le_top

theorem ker_determinant_le_ker_mul {χ η : GeneralLinear n F →* ℂˣ}
    (hχ : (determinant : GeneralLinear n F →* Fˣ).ker ≤ χ.ker)
    (hη : (determinant : GeneralLinear n F →* Fˣ).ker ≤ η.ker) :
    (determinant : GeneralLinear n F →* Fˣ).ker ≤ (χ * η).ker := by
  intro g hg
  change χ g * η g = 1
  rw [(χ.mem_ker).mp (hχ hg), (η.mem_ker).mp (hη hg), mul_one]

variable [TopologicalSpace F]

/-- Supercuspidality is unchanged by an open-kernel twist trivial on all conjugate
block unipotent radicals. -/
theorem isSupercuspidal_twist_iff_of_le_ker {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (χ : GeneralLinear n F →* ℂˣ) (hχ : IsOpen (χ.ker : Set (GeneralLinear n F)))
    (hU : ∀ (B : BlockShape n) (g : GeneralLinear n F), B.conjugateUnipotent g ≤ χ.ker)
    (ρ : Representation ℂ (GeneralLinear n F) V) :
    IsSupercuspidal (twist χ ρ) ↔ IsSupercuspidal ρ := by
  unfold IsSupercuspidal
  rw [isAdmissible_twist_iff χ ρ hχ]
  refine and_congr Iff.rfl (forall_congr' fun B => forall_congr' fun _ => forall_congr' fun g => ?_)
  exact Jacquet.subsingleton_coinvariants_twist_iff χ ρ (hU B g)

/-- Supercuspidality is unchanged by an open-kernel character of the determinant. -/
theorem isSupercuspidal_twist_iff {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (χ : GeneralLinear n F →* ℂˣ) (hχ : IsOpen (χ.ker : Set (GeneralLinear n F)))
    (hdet : (determinant : GeneralLinear n F →* Fˣ).ker ≤ χ.ker)
    (ρ : Representation ℂ (GeneralLinear n F) V) :
    IsSupercuspidal (twist χ ρ) ↔ IsSupercuspidal ρ :=
  isSupercuspidal_twist_iff_of_le_ker χ hχ
    (fun B g => (B.conjugateUnipotent_le_ker_determinant g).trans hdet) ρ

namespace SupercuspidalRep

/-- The twist of an actual supercuspidal object by a character of the determinant. -/
def twist (χ : GeneralLinear n F →* ℂˣ) (hχ : IsOpen (χ.ker : Set (GeneralLinear n F)))
    (hdet : (determinant : GeneralLinear n F →* Fˣ).ker ≤ χ.ker)
    (A : SupercuspidalRep.{uF, uV} (F := F) (n := n)) :
    SupercuspidalRep.{uF, uV} (F := F) (n := n) :=
  ⟨A.obj.twist χ hχ, (SmoothRep.isIrreducible_twist_iff χ hχ A.obj).mpr A.property.1,
    (isSupercuspidal_twist_iff χ hχ hdet A.obj.representation).mpr A.property.2⟩

@[simp]
theorem twist_obj (χ : GeneralLinear n F →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (GeneralLinear n F)))
    (hdet : (determinant : GeneralLinear n F →* Fˣ).ker ≤ χ.ker)
    (A : SupercuspidalRep.{uF, uV} (F := F) (n := n)) :
    (twist χ hχ hdet A).obj = A.obj.twist χ hχ := rfl

/-- Twisting restricted to the full supercuspidal subcategory. -/
def twistFunctor (χ : GeneralLinear n F →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (GeneralLinear n F)))
    (hdet : (determinant : GeneralLinear n F →* Fˣ).ker ≤ χ.ker) :
    SupercuspidalRep.{uF, uV} (F := F) (n := n) ⥤
      SupercuspidalRep.{uF, uV} (F := F) (n := n) :=
  ObjectProperty.lift _
    ((supercuspidalProperty (F := F) (n := n)).ι ⋙ SmoothRep.twistFunctor χ hχ)
    (fun A => (twist χ hχ hdet A).property)

@[simp]
theorem twistFunctor_obj (χ : GeneralLinear n F →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (GeneralLinear n F)))
    (hdet : (determinant : GeneralLinear n F →* Fˣ).ker ≤ χ.ker)
    (A : SupercuspidalRep.{uF, uV} (F := F) (n := n)) :
    (twistFunctor χ hχ hdet).obj A = twist χ hχ hdet A := rfl

/-- Lift an isomorphism of underlying smooth objects to the full subcategory. -/
def isoMk {A B : SupercuspidalRep.{uF, uV} (F := F) (n := n)} (e : A.obj ≅ B.obj) :
    A ≅ B :=
  ObjectProperty.isoMk _ e

end SupercuspidalRep

namespace SupercuspidalClass

/-- Twisting supercuspidal isomorphism classes by a character of the determinant. -/
def twist (χ : GeneralLinear n F →* ℂˣ) (hχ : IsOpen (χ.ker : Set (GeneralLinear n F)))
    (hdet : (determinant : GeneralLinear n F →* Fˣ).ker ≤ χ.ker) :
    SupercuspidalClass.{uV, uF} (F := F) (n := n) →
      SupercuspidalClass.{uV, uF} (F := F) (n := n) :=
  Quotient.map (SupercuspidalRep.twist χ hχ hdet)
    (fun _ _ ⟨e⟩ => ⟨(SupercuspidalRep.twistFunctor χ hχ hdet).mapIso e⟩)

@[simp]
theorem twist_isoClass (χ : GeneralLinear n F →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (GeneralLinear n F)))
    (hdet : (determinant : GeneralLinear n F →* Fˣ).ker ≤ χ.ker)
    (A : SupercuspidalRep.{uF, uV} (F := F) (n := n)) :
    twist χ hχ hdet A.isoClass = (SupercuspidalRep.twist χ hχ hdet A).isoClass := rfl

theorem twist_one (h1 : IsOpen ((1 : GeneralLinear n F →* ℂˣ).ker : Set (GeneralLinear n F)))
    (a : SupercuspidalClass.{uV, uF} (F := F) (n := n)) :
    twist 1 h1 ker_determinant_le_ker_one a = a := by
  induction a using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨SupercuspidalRep.isoMk (SmoothRep.twistOneIso h1 A.obj)⟩

theorem twist_twist (χ η : GeneralLinear n F →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (GeneralLinear n F)))
    (hη : IsOpen (η.ker : Set (GeneralLinear n F)))
    (hχη : IsOpen ((χ * η).ker : Set (GeneralLinear n F)))
    (hdetχ : (determinant : GeneralLinear n F →* Fˣ).ker ≤ χ.ker)
    (hdetη : (determinant : GeneralLinear n F →* Fˣ).ker ≤ η.ker)
    (a : SupercuspidalClass.{uV, uF} (F := F) (n := n)) :
    twist χ hχ hdetχ (twist η hη hdetη a) =
      twist (χ * η) hχη (ker_determinant_le_ker_mul hdetχ hdetη) a := by
  induction a using Quotient.inductionOn with
  | h A =>
    exact Quotient.sound
      ⟨SupercuspidalRep.isoMk (SmoothRep.twistTwistIso χ η hχ hη hχη A.obj)⟩

/-- Forgetting supercuspidality commutes with twisting. -/
theorem toSmoothDualClass_twist (χ : GeneralLinear n F →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (GeneralLinear n F)))
    (hdet : (determinant : GeneralLinear n F →* Fˣ).ker ≤ χ.ker)
    (a : SupercuspidalClass.{uV, uF} (F := F) (n := n)) :
    (twist χ hχ hdet a).toSmoothDualClass = SmoothDualClass.twist χ hχ a.toSmoothDualClass := by
  induction a using Quotient.inductionOn with
  | h A => rfl

end SupercuspidalClass

end GeneralLinear

namespace PadicField

variable {p : ℕ} [Fact p.Prime]

namespace TopologicalData

variable {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The complex character `g ↦ |det g|^s` with the residue-normalized absolute value. -/
abbrev determinantPowerCharacter (n : ℕ) (s : ℝ) : GeneralLinear n F.Carrier →* ℂˣ :=
  realPowerCharacter (T.determinantNorm n) s

/-- Worker 167's determinant-power norm calculation, with the rank retained. -/
theorem norm_determinantPowerCharacter_scalar (n : ℕ) (s : ℝ)
    (z : F.Carrierˣ) :
    ‖(T.determinantPowerCharacter n s (GeneralLinear.scalar z) : ℂ)‖ =
      T.normalizedAbs z ^ ((n : ℝ) * s) := by
  rw [coe_realPowerCharacter, T.determinantNorm_scalar]
  change ‖(((T.normalizedAbs z ^ n) ^ s : ℝ) : ℂ)‖ = _
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (pow_nonneg (T.normalizedAbs_nonneg _) _) _),
    ← Real.rpow_natCast_mul (T.normalizedAbs_nonneg _)]

theorem isOpen_ker_determinantPowerCharacter (n : ℕ) (s : ℝ) :
    letI := T.topology
    IsOpen ((T.determinantPowerCharacter n s).ker : Set (GeneralLinear n F.Carrier)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  exact isOpen_ker_realPowerCharacter _ (T.isOpen_ker_determinantNorm n) s

theorem ker_determinant_le_ker_determinantPowerCharacter (n : ℕ) (s : ℝ) :
    (GeneralLinear.determinant : GeneralLinear n F.Carrier →* F.Carrierˣ).ker ≤
      (T.determinantPowerCharacter n s).ker :=
  (GeneralLinear.ker_determinant_le_ker_comp T.normalizedAbsUnits).trans
    (ker_le_realPowerCharacter_ker (T.determinantNorm n) s)

/-- The twist `A ↦ A ⊗ |det|^s` of supercuspidal classes for the topology of `T`. -/
def supercuspidalClassRealPowerTwist (n : ℕ) (s : ℝ) :
    letI := T.topology
    GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := n) →
      GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := n) :=
  letI := T.topology
  GeneralLinear.SupercuspidalClass.twist (T.determinantPowerCharacter n s)
    (T.isOpen_ker_determinantPowerCharacter n s)
    (T.ker_determinant_le_ker_determinantPowerCharacter n s)

end TopologicalData

/-- The twist `A ↦ A ⊗ |det|^s` on the canonical p-adic supercuspidal class space. -/
def SupercuspidalClass.realPowerTwist {F : PadicField.{uF} p} {n : ℕ} {hn : 0 < n}
    (s : ℝ) :
    SupercuspidalClass.{uV, uF} F n hn → SupercuspidalClass.{uV, uF} F n hn :=
  F.canonicalTopologicalData.supercuspidalClassRealPowerTwist n s

end PadicField

end Langlands
