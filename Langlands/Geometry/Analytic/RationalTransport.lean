import Langlands.Geometry.Analytic.RationalTransport.Statement
import Langlands.Geometry.Analytic.RationalPresentation

/-! # Transport of actual rational quotients across base presentations -/

noncomputable section

universe u

namespace Langlands.Analytic.RationalPresentation

open StrictTateAlgebra PresentedStrictAffinoidAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (n m : ℕ) (S : Set (StrictTateAlgebra (Fin n) K))
  (g : StrictTateAlgebra (Fin n) K) (f : Fin m → StrictTateAlgebra (Fin n) K)

/-- Restriction to the base and the new coordinates determines a map out of
the rational quotient, even without the unit-ideal condition. -/
theorem hom_ext_base_coordinates (B : Type*) [NormedCommRing B] [NormedAlgebra K B]
    (φ ψ : BoundedAlgHom K (algebra K n m S g f) B)
    (hbase : φ.comp (baseMap K n m S g f) = ψ.comp (baseMap K n m S g f))
    (hnew : ∀ j, φ (coordinate K (algebra K n m S g f) (Fin.natAdd n j)) =
      ψ (coordinate K (algebra K n m S g f) (Fin.natAdd n j))) : φ = ψ := by
  apply hom_ext_coordinates K (n + m) (relations K n m S g f) B
  intro i
  refine Fin.addCases (fun i => ?_) (fun j => hnew j) i
  exact (congrArg φ (baseMap_coordinate K n m S g f i)).symm.trans
    ((congrArg (fun χ => χ (coordinate K (ofRelations K n S) i)) hbase).trans
      (congrArg ψ (baseMap_coordinate K n m S g f i)))

/-- The newly adjoined coordinates have bounded monomials in the actual
quotient norm. No bound on spectral values is converted into a norm bound. -/
theorem newCoordinates_bounded :
    HasBoundedMonomials (Fin m) (algebra K n m S g f)
      (fun j => coordinate K (algebra K n m S g f) (Fin.natAdd n j)) := by
  apply (hasBoundedMonomials_iff_pow_bound _ _ _).mpr
  intro j
  exact (hasBoundedMonomials_map_X (Fin (n + m)) K (algebra K n m S g f)
    (presentationMap K (algebra K n m S g f))).pow_bound
      (Fin (n + m)) (algebra K n m S g f) (Fin.natAdd n j)

variable (n' : ℕ) (S' : Set (StrictTateAlgebra (Fin n') K))
  (g' : StrictTateAlgebra (Fin n') K) (f' : Fin m → StrictTateAlgebra (Fin n') K)

/-- Transport a base map preserving the displayed quotient elements to the
actual rational quotients, by convergent evaluation at the target coordinates. -/
def map (φ : BoundedAlgHom K (ofRelations K n S) (ofRelations K n' S'))
    (hg : φ (presentationMap K (ofRelations K n S) g) =
      presentationMap K (ofRelations K n' S') g')
    (hf : ∀ j, φ (presentationMap K (ofRelations K n S) (f j)) =
      presentationMap K (ofRelations K n' S') (f' j)) :
    BoundedAlgHom K (algebra K n m S g f) (algebra K n' m S' g' f') :=
  liftFromBase K n m S g f (algebra K n' m S' g' f')
    ((baseMap K n' m S' g' f').comp φ)
    (fun j => coordinate K (algebra K n' m S' g' f') (Fin.natAdd n' j))
    (newCoordinates_bounded K n' m S' g' f') (fun j => by
      change baseMap K n' m S' g' f' (φ (presentationMap K (ofRelations K n S) g)) *
        coordinate K (algebra K n' m S' g' f') (Fin.natAdd n' j) =
          baseMap K n' m S' g' f' (φ (presentationMap K (ofRelations K n S) (f j)))
      rw [hg, hf j]
      exact coordinate_equation K n' m S' g' f' j)

theorem map_comp_baseMap
    (φ : BoundedAlgHom K (ofRelations K n S) (ofRelations K n' S'))
    (hg : φ (presentationMap K (ofRelations K n S) g) =
      presentationMap K (ofRelations K n' S') g')
    (hf : ∀ j, φ (presentationMap K (ofRelations K n S) (f j)) =
      presentationMap K (ofRelations K n' S') (f' j)) :
    (map K n m S g f n' S' g' f' φ hg hf).comp (baseMap K n m S g f) =
      (baseMap K n' m S' g' f').comp φ :=
  liftFromBase_comp_baseMap K n m S g f _ _ _ _ _

theorem map_newCoordinate
    (φ : BoundedAlgHom K (ofRelations K n S) (ofRelations K n' S'))
    (hg : φ (presentationMap K (ofRelations K n S) g) =
      presentationMap K (ofRelations K n' S') g')
    (hf : ∀ j, φ (presentationMap K (ofRelations K n S) (f j)) =
      presentationMap K (ofRelations K n' S') (f' j)) (j : Fin m) :
    map K n m S g f n' S' g' f' φ hg hf
      (coordinate K (algebra K n m S g f) (Fin.natAdd n j)) =
        coordinate K (algebra K n' m S' g' f') (Fin.natAdd n' j) :=
  liftFromBase_coordinate K n m S g f _ _ _ _ _ j

/-- Mutually inverse maps of the base give mutually inverse rational maps.
The proof uses the base and coordinate equations, not a spectral argument. -/
theorem map_leftInverse
    (φ : BoundedAlgHom K (ofRelations K n S) (ofRelations K n' S'))
    (ψ : BoundedAlgHom K (ofRelations K n' S') (ofRelations K n S))
    (hg : φ (presentationMap K (ofRelations K n S) g) =
      presentationMap K (ofRelations K n' S') g')
    (hf : ∀ j, φ (presentationMap K (ofRelations K n S) (f j)) =
      presentationMap K (ofRelations K n' S') (f' j))
    (hg' : ψ (presentationMap K (ofRelations K n' S') g') =
      presentationMap K (ofRelations K n S) g)
    (hf' : ∀ j, ψ (presentationMap K (ofRelations K n' S') (f' j)) =
      presentationMap K (ofRelations K n S) (f j))
    (hinv : ∀ a, ψ (φ a) = a) :
    Function.LeftInverse (map K n' m S' g' f' n S g f ψ hg' hf')
      (map K n m S g f n' S' g' f' φ hg hf) := by
  have h :
      (map K n' m S' g' f' n S g f ψ hg' hf').comp
        (map K n m S g f n' S' g' f' φ hg hf) =
          BoundedAlgHom.id K (algebra K n m S g f) := by
    apply hom_ext_base_coordinates K n m S g f (algebra K n m S g f)
    · apply BoundedAlgHom.ext
      intro a
      have hφ := congrArg (fun χ => χ a)
        (map_comp_baseMap K n m S g f n' S' g' f' φ hg hf)
      have hψ := congrArg (fun χ => χ (φ a))
        (map_comp_baseMap K n' m S' g' f' n S g f ψ hg' hf')
      change map K n m S g f n' S' g' f' φ hg hf (baseMap K n m S g f a) =
        baseMap K n' m S' g' f' (φ a) at hφ
      change map K n' m S' g' f' n S g f ψ hg' hf'
          (baseMap K n' m S' g' f' (φ a)) =
        baseMap K n m S g f (ψ (φ a)) at hψ
      change map K n' m S' g' f' n S g f ψ hg' hf'
        (map K n m S g f n' S' g' f' φ hg hf (baseMap K n m S g f a)) =
          baseMap K n m S g f a
      rw [hφ, hψ, hinv]
    · intro j
      change map K n' m S' g' f' n S g f ψ hg' hf'
        (map K n m S g f n' S' g' f' φ hg hf
          (coordinate K (algebra K n m S g f) (Fin.natAdd n j))) = _
      rw [map_newCoordinate, map_newCoordinate]
      rfl
  exact fun a => congrArg (fun χ => χ a) h

/-- A bounded equivalence of base presentations carrying the actual
denominator and numerator elements induces a bounded equivalence of
the actual rational quotient algebras. -/
def equiv (e : BoundedAlgEquiv K (ofRelations K n S) (ofRelations K n' S'))
    (hg : e (presentationMap K (ofRelations K n S) g) =
      presentationMap K (ofRelations K n' S') g')
    (hf : ∀ j, e (presentationMap K (ofRelations K n S) (f j)) =
      presentationMap K (ofRelations K n' S') (f' j)) :
    BoundedAlgEquiv K (algebra K n m S g f) (algebra K n' m S' g' f') := by
  have hg' : e.symm (presentationMap K (ofRelations K n' S') g') =
      presentationMap K (ofRelations K n S) g := by
    simpa only [BoundedAlgEquiv.symm_apply_apply] using (congrArg e.symm hg).symm
  have hf' : ∀ j, e.symm (presentationMap K (ofRelations K n' S') (f' j)) =
      presentationMap K (ofRelations K n S) (f j) := fun j => by
    simpa only [BoundedAlgEquiv.symm_apply_apply] using (congrArg e.symm (hf j)).symm
  exact BoundedAlgEquiv.ofHomInv
    (map K n m S g f n' S' g' f' e.toBoundedAlgHom hg hf)
    (map K n' m S' g' f' n S g f e.symm.toBoundedAlgHom hg' hf')
    (map_leftInverse K n m S g f n' S' g' f' _ _ hg hf hg' hf'
      e.symm_apply_apply)
    (map_leftInverse K n' m S' g' f' n S g f _ _ hg' hf' hg hf
      e.apply_symm_apply)

theorem equiv_comp_baseMap
    (e : BoundedAlgEquiv K (ofRelations K n S) (ofRelations K n' S'))
    (hg : e (presentationMap K (ofRelations K n S) g) =
      presentationMap K (ofRelations K n' S') g')
    (hf : ∀ j, e (presentationMap K (ofRelations K n S) (f j)) =
      presentationMap K (ofRelations K n' S') (f' j)) :
    (equiv K n m S g f n' S' g' f' e hg hf).toBoundedAlgHom.comp
      (baseMap K n m S g f) =
        (baseMap K n' m S' g' f').comp e.toBoundedAlgHom :=
  map_comp_baseMap K n m S g f n' S' g' f' _ hg hf

theorem equiv_newCoordinate
    (e : BoundedAlgEquiv K (ofRelations K n S) (ofRelations K n' S'))
    (hg : e (presentationMap K (ofRelations K n S) g) =
      presentationMap K (ofRelations K n' S') g')
    (hf : ∀ j, e (presentationMap K (ofRelations K n S) (f j)) =
      presentationMap K (ofRelations K n' S') (f' j)) (j : Fin m) :
    equiv K n m S g f n' S' g' f' e hg hf
      (coordinate K (algebra K n m S g f) (Fin.natAdd n j)) =
        coordinate K (algebra K n' m S' g' f') (Fin.natAdd n' j) :=
  map_newCoordinate K n m S g f n' S' g' f' _ hg hf j

/-- Equal quotient elements give equivalent rational algebras for any choice
of Tate-series lifts. No unit-ideal hypothesis is needed for this independence. -/
def equivOfLifts (g' : StrictTateAlgebra (Fin n) K)
    (f' : Fin m → StrictTateAlgebra (Fin n) K)
    (hg : presentationMap K (ofRelations K n S) g =
      presentationMap K (ofRelations K n S) g')
    (hf : ∀ j, presentationMap K (ofRelations K n S) (f j) =
      presentationMap K (ofRelations K n S) (f' j)) :
    BoundedAlgEquiv K (algebra K n m S g f) (algebra K n m S g' f') :=
  equiv K n m S g f n S g' f' (BoundedAlgEquiv.refl K _) hg hf

/-- The equivalence of rational spectra lies over the equivalence of base
spectra. This identifies both the points and their topology. -/
theorem spectrum_equiv_over_base
    (e : BoundedAlgEquiv K (ofRelations K n S) (ofRelations K n' S'))
    (hg : e (presentationMap K (ofRelations K n S) g) =
      presentationMap K (ofRelations K n' S') g')
    (hf : ∀ j, e (presentationMap K (ofRelations K n S) (f j)) =
      presentationMap K (ofRelations K n' S') (f' j))
    (x : BanachSpectrum (algebra K n' m S' g' f')) :
    BanachSpectrum.comap (baseMap K n m S g f).toBoundedRingHom
        ((equiv K n m S g f n' S' g' f' e hg hf).spectrumHomeomorph x) =
      e.spectrumHomeomorph
        (BanachSpectrum.comap (baseMap K n' m S' g' f').toBoundedRingHom x) := by
  apply BanachSpectrum.ext
  intro a
  exact congrArg x (congrArg (fun χ => χ a)
    (equiv_comp_baseMap K n m S g f n' S' g' f' e hg hf))

/-- Bounded quotient transport and equivalences, with no unit-ideal premise. -/
theorem transport : TransportStatement.{u} := by
  intro K _ _ _ n m S g f n' S' g' f'
  constructor
  · intro φ hg hf
    refine ⟨map K n m S g f n' S' g' f' φ hg hf,
      ⟨map_comp_baseMap K n m S g f n' S' g' f' φ hg hf,
        map_newCoordinate K n m S g f n' S' g' f' φ hg hf⟩, ?_⟩
    intro χ hχ
    apply hom_ext_base_coordinates K n m S g f (algebra K n' m S' g' f')
    · exact hχ.1.trans (map_comp_baseMap K n m S g f n' S' g' f' φ hg hf).symm
    · intro j
      exact (hχ.2 j).trans
        (map_newCoordinate K n m S g f n' S' g' f' φ hg hf j).symm
  · intro e hg hf
    exact ⟨equiv K n m S g f n' S' g' f' e hg hf,
      equiv_comp_baseMap K n m S g f n' S' g' f' e hg hf,
      equiv_newCoordinate K n m S g f n' S' g' f' e hg hf,
      spectrum_equiv_over_base K n m S g f n' S' g' f' e hg hf⟩

end Langlands.Analytic.RationalPresentation
