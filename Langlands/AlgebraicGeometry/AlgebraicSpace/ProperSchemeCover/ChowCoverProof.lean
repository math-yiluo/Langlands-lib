import Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover.ChowCoverStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover.RelativeProper
import Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover.AffineEmbedding
import Langlands.AlgebraicGeometry.AlgebraicSpace.FinitePresentationEtaleAtlas
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianFinitePointProperProof

/-! # Proof of the weak Chow cover statement

Weak Chow data exist for every separated algebraic space over an affine base with a
quasi-compact locally finitely presented atlas. The chart is an affine atlas, embedded as a
closed subscheme of the standard open `D₊(X₀)` of a projective space `ℙᴺ`. The proper scheme
`M` is the fibre product over the base of `n + 1` copies of `ℙᴺ`. The construction of the
modules `Construction`, `Closedness` and `RelativeProper` then proves `ChowCoverStatement`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover

namespace ChowData

variable {S : Scheme.{u}} {X : AlgebraicSpace S} (D : ChowData X)

/-- Each open `opens i` of `Z` is quasi-compact. -/
theorem isCompact_opens (i : Fin (D.n + 1)) : IsCompact (D.opens i : Set D.Z.left) := by
  have : QuasiCompact ((D.ζ ≫ D.p i).left ≫ D.Y.hom) := by
    rw [Over.w]
    infer_instance
  have : QuasiCompact (D.ζ ≫ D.p i).left := QuasiCompact.of_comp _ D.Y.hom
  exact (D.ζ ≫ D.p i).left.isCompact_preimage (U := D.o.left.opensRange)
    (isCompact_range D.o.left.continuous)

instance : CompactSpace D.U.left := by
  refine isCompact_iff_compactSpace.mp ?_
  rw [TopologicalSpace.Opens.coe_iSup]
  exact isCompact_iUnion D.isCompact_opens

instance [IsAffine S] : QuasiCompact D.U.hom := inferInstance

end ChowData

/-- **Weak Chow covers exist.** -/
theorem chowCover : ChowCoverStatement.{u} := by
  intro S _ X hX hatlas
  obtain ⟨W, π, hW, hπe, hπs, hWfp⟩ := FinitePresentationEtaleAtlas.exists_affine_atlas hatlas
  have hqs : IsQuasiSeparated X :=
    HenselianFinitePointProperProof.isQuasiSeparated_of_isSeparated hX
  obtain ⟨n, hn⟩ := exists_completeLocus hqs hπe
  let C : Type u := Γ(S, ⊤)
  let e : S ≅ Spec (CommRingCat.of C) := S.isoSpec
  let s : W.left ⟶ Spec (CommRingCat.of C) := W.hom ≫ e.hom
  have : LocallyOfFiniteType s := by
    have : LocallyOfFiniteType W.hom := inferInstance
    infer_instance
  obtain ⟨N, ι₀, hι₀, hι₀s⟩ := exists_closedImmersion_stdAway C s
  let Y : Over S := Over.mk (ProjSpace.π C N ≫ e.inv)
  let O : Over S := Over.mk (stdAwayι C N ≫ Y.hom)
  let o : O ⟶ Y := Over.homMk (stdAwayι C N)
  let ιW : W ⟶ O := Over.homMk ι₀ (by
    change ι₀ ≫ stdAwayι C N ≫ ProjSpace.π C N ≫ e.inv = W.hom
    rw [reassoc_of% hι₀s]
    simp [s])
  let P := ChartFibrePower.fin hπe.1 n
  let M : Over S := Over.mk (ProjSpace.prodOverπ C (fun _ : Fin (n + 1) => N) ≫ e.inv)
  let p : Fin (n + 1) → (M ⟶ Y) := fun k =>
    Over.homMk (ProjSpace.prodPr C (fun _ : Fin (n + 1) => N) k) (by
      change ProjSpace.prodPr C (fun _ : Fin (n + 1) => N) k ≫ ProjSpace.π C N ≫ e.inv =
        ProjSpace.prodOverπ C (fun _ : Fin (n + 1) => N) ≫ e.inv
      rw [← Category.assoc]
      exact congrArg (· ≫ e.inv) (ProjSpace.prodPr_comp_π C (fun _ : Fin (n + 1) => N) k))
  have hg : ∀ k : Fin (n + 1),
      ((P.pr k).left ≫ ι₀ ≫ stdAwayι C N) ≫ ProjSpace.π C N = P.obj.hom ≫ e.hom := by
    intro k
    rw [Category.assoc, Category.assoc, hι₀s, ← Category.assoc, Over.w]
  let ε : P.obj ⟶ M :=
    Over.homMk (ProjSpace.prodLift C (P.obj.hom ≫ e.hom) (fun _ : Fin (n + 1) => N)
      (fun k => (P.pr k).left ≫ ι₀ ≫ stdAwayι C N) hg) (by
        change ProjSpace.prodLift C (P.obj.hom ≫ e.hom) (fun _ : Fin (n + 1) => N)
          (fun k => (P.pr k).left ≫ ι₀ ≫ stdAwayι C N) hg ≫
            ProjSpace.prodOverπ C (fun _ : Fin (n + 1) => N) ≫ e.inv = P.obj.hom
        rw [← Category.assoc, ProjSpace.prodLift_comp_prodOverπ, Category.assoc,
          Iso.hom_inv_id, Category.comp_id])
  let D : ChowData X :=
    { separated := hX
      W := W
      π := π
      etale := hπe
      surjective := hπs
      quasiCompact_W := inferInstance
      n := n
      P := P
      complete := hn
      Y := Y
      isSeparated_Y := by
        change _root_.AlgebraicGeometry.IsSeparated (ProjSpace.π C N ≫ e.inv)
        infer_instance
      O := O
      o := o
      isOpenImmersion_o := inferInstanceAs
        (_root_.AlgebraicGeometry.IsOpenImmersion (stdAwayι C N))
      compactSpace_O := inferInstanceAs (CompactSpace (Spec (stdAway C N)))
      ι := ιW
      isClosedImmersion_ι := hι₀
      M := M
      isProper_M := by
        change _root_.AlgebraicGeometry.IsProper
          (ProjSpace.prodOverπ C (fun _ : Fin (n + 1) => N) ≫ e.inv)
        infer_instance
      p := p
      ε := ε
      ε_p := fun k => by
        apply Over.OverMorphism.ext
        exact ProjSpace.prodLift_comp_prodPr C (P.obj.hom ≫ e.hom) (fun _ : Fin (n + 1) => N)
          (fun k => (P.pr k).left ≫ ι₀ ≫ stdAwayι C N) hg k }
  exact ⟨D.U, D.φ, D.isSurjective_φ, D.relative_isProper_φ, inferInstance, inferInstance⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover
