import Langlands.CommutativeAlgebra.DiagonalHopfEpiSurjective
import Langlands.GroupScheme.Torus.MultiplicativeTypeMonoClosedImmersionStatement
import Langlands.GroupScheme.Torus.ClosedImmersionLocusAffine
import Langlands.GroupScheme.Torus.AffineRelativeDiagonalizable
import Langlands.GroupScheme.Torus.DiagonalizableHopf
import Langlands.GroupScheme.Torus.IsomorphismLocus
import Langlands.AlgebraicGeometry.Morphisms.FppfLocalAtTarget
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Proof: monic homomorphisms from groups of multiplicative type are closed immersions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.MultiplicativeTypeMono

open TorusClosedImmersionLocus

/-- A ring map whose spectrum is a monomorphism of schemes is an epimorphism of rings. -/
theorem epi_of_mono_spec {A B : CommRingCat.{u}} (ψ : A ⟶ B) [Mono (Spec.map ψ)] : Epi ψ := by
  have : Mono (Scheme.Spec.map ψ.op) := ‹Mono (Spec.map ψ)›
  have : Mono ψ.op := Scheme.Spec.mono_of_mono_map this
  exact (op_mono_iff ψ).mp this

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]

/-- **Affine diagonal case.** A homomorphism from the standard diagonal Hopf spectrum
`Spec R[M]` into an affine group over `Spec R` whose underlying scheme map is a monomorphism is
a closed immersion. -/
theorem diagonalSource_isClosedImmersion {G : GroupScheme (Spec R)} [IsAffine G.X.left]
    (i : diagonalSource R M ⟶ G) [Mono i.hom.hom.left] : IsClosedImmersion i.hom.hom.left := by
  let φ := diagonalCoordinateMap i
  let ψ : CommRingCat.of (AffineCoordinates.hopfAlgebra G) ⟶
      CommRingCat.of (AddMonoidAlgebra R M) :=
    CommRingCat.ofHom φ.toAlgHom.toRingHom
  let eG := AffineCoordinates.hopfSpecIso G
  let heG : IsIso eG.inv.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso eG.inv
  have hmap : Spec.map ψ = i.hom.hom.left ≫ eG.inv.hom.hom.left := by
    change ((hopfSpec R).map (CommHopfAlgCat.ofHom φ).op).hom.hom.left = _
    rw [diagonalCoordinateMap_map]
    rfl
  have hmono : Mono (Spec.map ψ) := by
    rw [hmap]
    infer_instance
  have hepi : Epi ψ := epi_of_mono_spec ψ
  have hsurj : Function.Surjective φ := by
    refine CommutativeAlgebra.DiagonalHopfEpi.surjective_of_epi φ
      (fun x hx => AffineHomImageHopfAdapter.antipode_mem_range (CommHopfAlgCat.ofHom φ) x hx)
      ?_
    intro D _ f g hfg
    have h1 : ψ ≫ CommRingCat.ofHom f = ψ ≫ CommRingCat.ofHom g := by
      ext x
      exact RingHom.congr_fun hfg x
    exact congrArg CommRingCat.Hom.hom ((cancel_epi ψ).mp h1)
  have hc : IsClosedImmersion (Spec.map ψ) := IsClosedImmersion.spec_of_surjective ψ hsurj
  rw [hmap, MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion)] at hc
  exact hc

/-- **Affine diagonalizable case.** Over an affine base, a homomorphism from a diagonalizable
group into an affine group whose underlying scheme map is a monomorphism is a closed
immersion. -/
theorem isClosedSubgroup_of_isDiagonalizable_affine {H G : GroupScheme (Spec R)}
    [IsAffine G.X.left] (hH : RelativeMultiplicativeType.IsDiagonalizable H) (j : H ⟶ G)
    [Mono j.hom.hom.left] : IsClosedSubgroup j := by
  obtain ⟨Λ, _, _, ⟨e⟩⟩ := hH
  let e' : diagonalSource R Λ ≅ H :=
    Diagonalizable.hopfSpecIso R Λ ≪≫ Diagonalizable.relativeModelIso R Λ ≪≫ e.symm
  let he : IsIso e'.hom.hom.hom.left := (Grp.forget _ ⋙ Over.forget _).map_isIso e'.hom
  have : Mono (e'.hom ≫ j).hom.hom.left := by
    change Mono (e'.hom.hom.hom.left ≫ j.hom.hom.left)
    infer_instance
  have hc := diagonalSource_isClosedImmersion (e'.hom ≫ j)
  change IsClosedImmersion (e'.hom.hom.hom.left ≫ j.hom.hom.left) at hc
  rwa [MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)] at hc

/-- **Diagonalizable case over an arbitrary base.** A homomorphism from a diagonalizable group
into an affine group over `S`, monic over `S`, is a closed immersion. The proof checks this on
the base change to the members of an affine open cover of `S`. -/
theorem isClosedSubgroup_of_isDiagonalizable {S : Scheme.{u}} {H G : GroupScheme S}
    [IsAffineHom G.X.hom] (hH : RelativeMultiplicativeType.IsDiagonalizable H) (j : H ⟶ G)
    [Mono j.hom.hom] : IsClosedSubgroup j := by
  let C := S.affineOpenCover.openCover
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) (C.pullback₁ G.X.hom)
  intro s
  let b := C.f s
  have hp := TorusIsomorphismLocus.underlying_isPullback b j
  change IsClosedImmersion (pullback.snd j.hom.hom.left (pullback.fst G.X.hom b))
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    hp.isoPullback.hom, hp.isoPullback_hom_snd]
  let Gb := (baseChange b).obj G
  let : IsAffineHom Gb.X.hom := MorphismProperty.pullback_snd G.X.hom b inferInstance
  have : IsAffine Gb.X.left := isAffine_of_isAffineHom Gb.X.hom
  have hm : Mono ((baseChange b).map j).hom.hom :=
    (inferInstance : Mono ((Over.pullback b).map j.hom.hom))
  have : Mono ((baseChange b).map j).hom.hom.left := Over.mono_left_of_mono _
  exact isClosedSubgroup_of_isDiagonalizable_affine (R := S.affineOpenCover.X s)
    (hH.baseChange b) ((baseChange b).map j)

end MultiplicativeTypeMono

/-- **Monic homomorphisms from groups of multiplicative type are closed immersions**
(Conrad, *Reductive group schemes* (2014), Lemma B.1.3). -/
theorem multiplicativeTypeMonoClosedImmersion :
    MultiplicativeTypeMonoClosedImmersionStatement.{u} := by
  intro S G H _ _ j hH hj
  obtain ⟨𝒰, h𝒰⟩ := hH
  unfold IsClosedSubgroup
  rw [IsClosedImmersion.iff_isProper_and_mono]
  refine ⟨?_, inferInstance⟩
  have := Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage @IsProper
  have : Precoverage.HasPullbacks Scheme.fppfPrecoverage.{u} :=
    inferInstanceAs (Precoverage.HasPullbacks
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)))
  let 𝒱 : Scheme.Cover.{u} Scheme.fppfPrecoverage G.X.left := 𝒰.pullback₁ G.X.hom
  refine MorphismProperty.IsLocalAtTarget.of_zeroHypercover 𝒱 fun i => ?_
  let b := 𝒰.f i
  change IsProper (pullback.snd j.hom.hom.left (pullback.fst G.X.hom b))
  have hp := TorusIsomorphismLocus.underlying_isPullback b j
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsProper)
    hp.isoPullback.hom, hp.isoPullback_hom_snd]
  let Gb := (baseChange b).obj G
  let : IsAffineHom Gb.X.hom := MorphismProperty.pullback_snd G.X.hom b inferInstance
  have : Mono ((baseChange b).map j).hom.hom :=
    (inferInstance : Mono ((Over.pullback b).map j.hom.hom))
  have hc : IsClosedImmersion ((baseChange b).map j).hom.hom.left :=
    MultiplicativeTypeMono.isClosedSubgroup_of_isDiagonalizable (h𝒰 i) ((baseChange b).map j)
  infer_instance

end Langlands.GroupScheme
