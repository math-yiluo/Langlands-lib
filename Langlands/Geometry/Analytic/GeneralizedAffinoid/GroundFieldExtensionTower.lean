import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtension

/-! # Direct and successive ground field extension of affinoid algebras -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (L : Type v) [NormedField L] [IsUltrametricDist L] [NormedAlgebra K L]
  (M : Type w) [NormedField M] [IsUltrametricDist M] [CompleteSpace M]
  [NormedAlgebra L M] [NormedAlgebra K M] [IsScalarTower K L M]

omit [IsUltrametricDist K] [IsUltrametricDist L] [IsUltrametricDist M] [CompleteSpace M] in
private theorem towerThroughMiddle (E : Type*) [CommRing E]
    [Algebra K E] [Algebra L E] [Algebra M E]
    [IsScalarTower K M E] [IsScalarTower L M E] : IsScalarTower K L E :=
  IsScalarTower.of_algebraMap_eq fun x =>
    (IsScalarTower.algebraMap_apply K M E x).trans
      (congrArg (algebraMap M E) (IsScalarTower.algebraMap_apply K L M x)) |>.trans
        (IsScalarTower.algebraMap_apply L M E (algebraMap K L x)).symm

section Equivalence

variable (A : PresentedAffinoidAlgebra K)

local notation "AL" => algebra K L A
local notation "Direct" => algebra K M A
local notation "Successive" => algebra L M (algebra K L A)

private local instance : NormedAlgebra L Direct := NormedAlgebra.restrictScalars L M Direct

private local instance : IsScalarTower L M Direct := IsScalarTower.of_algebraMap_eq' rfl

private local instance : IsScalarTower K L Direct := towerThroughMiddle K L M Direct

private local instance : NormedAlgebra K Successive :=
  NormedAlgebra.restrictScalars K M Successive

private local instance : IsScalarTower K M Successive := IsScalarTower.of_algebraMap_eq' rfl

private local instance : IsScalarTower K L Successive := towerThroughMiddle K L M Successive

private def towerHom : BoundedAlgHom M Successive Direct :=
  lift L M AL Direct (lift K L A Direct (iota K M A))

private def towerInv : BoundedAlgHom M Direct Successive :=
  lift K M A Successive ((overBase K L (iota L M AL)).comp (iota K L A))

private theorem towerHom_coordinate (i : Fin A.arity) :
    towerHom K L M A (coordinate M Successive i) = coordinate M Direct i := by
  exact (lift_coordinate L M AL Direct (lift K L A Direct (iota K M A)) i).trans
    ((lift_coordinate K L A Direct (iota K M A) i).trans (iota_coordinate K M A i))

private theorem towerInv_coordinate (i : Fin A.arity) :
    towerInv K L M A (coordinate M Direct i) = coordinate M Successive i :=
  (lift_coordinate K M A Successive
    ((overBase K L (iota L M AL)).comp (iota K L A)) i).trans
    ((congrArg (fun x : AL => iota L M AL x) (iota_coordinate K L A i)).trans
      (iota_coordinate L M AL i))

/-- The bounded equivalence `(A_L)_M ≃ A_M` obtained by the universal property. -/
def towerEquiv : BoundedAlgEquiv M Successive Direct := by
  have hleft : (towerInv K L M A).comp (towerHom K L M A) =
      BoundedAlgHom.id M Successive := by
    apply hom_ext_coordinate M Successive Successive
    intro i
    exact (congrArg (fun x : Direct => towerInv K L M A x)
      (towerHom_coordinate K L M A i)).trans (towerInv_coordinate K L M A i)
  have hright : (towerHom K L M A).comp (towerInv K L M A) =
      BoundedAlgHom.id M Direct := by
    apply hom_ext_coordinate M Direct Direct
    intro i
    exact (congrArg (fun x : Successive => towerHom K L M A x)
      (towerInv_coordinate K L M A i)).trans (towerHom_coordinate K L M A i)
  exact BoundedAlgEquiv.ofHomInv (towerHom K L M A) (towerInv K L M A)
    (fun a => congrArg (fun φ : BoundedAlgHom M Successive Successive => φ a) hleft)
    (fun a => congrArg (fun φ : BoundedAlgHom M Direct Direct => φ a) hright)

/-- The comparison takes every original coefficient to its direct image. -/
@[simp] theorem towerEquiv_iota (a : A) :
    towerEquiv K L M A (iota L M AL (iota K L A a)) = iota K M A a := by
  change towerHom K L M A (iota L M AL (iota K L A a)) = _
  unfold towerHom
  rw [lift_iota, lift_iota]

@[simp] theorem towerEquiv_coordinate (i : Fin A.arity) :
    towerEquiv K L M A (coordinate M Successive i) = coordinate M Direct i :=
  towerHom_coordinate K L M A i

/-- The homeomorphism from the directly extended spectrum to the successively
extended spectrum, contravariantly induced by the bounded equivalence. -/
def towerSpectrumHomeomorph : BanachSpectrum Direct ≃ₜ BanachSpectrum Successive :=
  (towerEquiv K L M A).spectrumHomeomorph

@[simp] theorem towerSpectrumHomeomorph_apply (x : BanachSpectrum Direct) (a : Successive) :
    towerSpectrumHomeomorph K L M A x a = x (towerEquiv K L M A a) := rfl

/-- Both paths from the directly extended spectrum to the original agree. -/
theorem towerSpectrumHomeomorph_projection (x : BanachSpectrum Direct) :
    spectrumProjection K L A
        (spectrumProjection L M AL (towerSpectrumHomeomorph K L M A x)) =
      spectrumProjection K M A x := by
  apply BanachSpectrum.ext
  intro a
  change x (towerEquiv K L M A (iota L M AL (iota K L A a))) = x (iota K M A a)
  rw [towerEquiv_iota]

end Equivalence

variable [CompleteSpace L] {A B : PresentedAffinoidAlgebra K}

/-- Naturality of the tower comparison for every actual bounded algebra map. -/
theorem towerEquiv_naturality (f : BoundedAlgHom K A B) :
    (towerEquiv K L M B).toBoundedAlgHom.comp (map L M (map K L f)) =
      (map K M f).comp (towerEquiv K L M A).toBoundedAlgHom := by
  apply hom_ext_coordinate M (algebra K M B) (algebra L M (algebra K L A))
  intro i
  have hmap : map L M (map K L f) (coordinate M (algebra L M (algebra K L A)) i) =
      iota L M (algebra K L B) (iota K L B (f (coordinate K A i))) :=
    (map_coordinate (L := M) (map K L f) i).trans
      (congrArg (fun b : algebra K L B => iota L M (algebra K L B) b)
        (map_coordinate (L := L) f i))
  exact ((congrArg (fun b : algebra L M (algebra K L B) => towerEquiv K L M B b) hmap).trans
    (towerEquiv_iota K L M B (f (coordinate K A i)))).trans
    (((congrArg (fun a : algebra K M A => map K M f a) (towerEquiv_coordinate K L M A i)).trans
      (map_coordinate (L := M) f i)).symm)

/-- Naturality of the corresponding homeomorphism on spectra. -/
theorem towerSpectrumHomeomorph_naturality (f : BoundedAlgHom K A B)
    (x : BanachSpectrum (algebra K M B)) :
    towerSpectrumHomeomorph K L M A (BanachSpectrum.comap (map K M f).toBoundedRingHom x) =
      BanachSpectrum.comap (map L M (map K L f)).toBoundedRingHom
        (towerSpectrumHomeomorph K L M B x) := by
  apply BanachSpectrum.ext
  intro a
  change x (map K M f (towerEquiv K L M A a)) =
    x (towerEquiv K L M B (map L M (map K L f) a))
  exact congrArg (fun b : algebra K M B => x b)
    (congrArg (fun φ : BoundedAlgHom M (algebra L M (algebra K L A)) (algebra K M B) => φ a)
      (towerEquiv_naturality K L M f)).symm

end Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension
