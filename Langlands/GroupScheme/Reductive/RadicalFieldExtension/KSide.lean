import Langlands.GroupScheme.Reductive.RadicalFieldExtension.Laws
import Langlands.GroupScheme.Reductive.RadicalFieldExtension.RationalSideInterface
import Langlands.GroupScheme.Reductive.RadicalFieldExtensionStatement
import Langlands.GroupScheme.Absolute.BorelFieldExtensionMaximality
import Langlands.GroupScheme.Absolute.UnipotentPointsSolvable
import Langlands.GroupScheme.Absolute.RationalSubgroupContainment
import Langlands.GroupScheme.Rational.UnipotentProductBound
import Langlands.GroupScheme.Dynamic.GeneralLinearBaseChange
import Langlands.GroupScheme.UnitSubgroup
import Langlands.GroupScheme.CorepresentedSmooth
import Langlands.AbelianScheme.KernelBaseChange

/-! # Trivial unipotent radical after an extension of algebraically closed fields

The `K`-side of the proof. A smooth connected unipotent normal closed subgroup of the base
change of `G` gives a normal solvable group of `K`-points acting unipotently in a fixed closed
embedding `G → GL_N`. If it is nontrivial, the algebraic core of `Laws` specializes it to the
data of `RationalSideStatement` over `k`. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open WithConv

namespace Langlands.GroupScheme.RadicalFieldExtension

open BorelFieldExtension

set_option backward.isDefEq.respectTransparency false

section Matrix

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} {n : Type} [Fintype n] [DecidableEq n]

/-- The entries of `(ρ(z) - 1)^m` at a point `z` are the pullbacks of the entries of
`(M - 1)^m`, for `M` the universal matrix of `ρ`. -/
theorem pointMatrix_sub_one_pow_apply (ρ : MatrixRepresentation G n) (m : ℕ) {T : Over (Spec R)}
    (z : T ⟶ G.X) (a b : n) :
    (((ρ.pointMatrix T z : Matrix n n Γ(T.left, ⊤)) - 1) ^ m) a b =
      z.left.appTop ((((ρ.pointMatrix G.X (𝟙 G.X) : Matrix n n Γ(G.X.left, ⊤)) - 1) ^ m) a b) := by
  have h := ρ.pointMatrix_naturality z (𝟙 G.X)
  rw [Category.comp_id] at h
  have h' : ((ρ.pointMatrix T z : Matrix n n Γ(T.left, ⊤)) - 1) ^ m =
      z.left.appTop.hom.mapMatrix
        (((ρ.pointMatrix G.X (𝟙 G.X) : Matrix n n Γ(G.X.left, ⊤)) - 1) ^ m) := by
    rw [map_pow, map_sub, map_one, h]
    rfl
  exact congrFun (congrFun h' a) b

end Matrix

section Unit

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H]

/-- A point killing the augmentation ideal is the identity. -/
theorem eq_one_of_ker_le {A : Type u} [CommRing A] [Algebra k A] (x : H →ₐ[k] A)
    (hx : RingHom.ker (1 : WithConv (H →ₐ[k] k)).ofConv ≤ RingHom.ker x) :
    x = (1 : WithConv (H →ₐ[k] A)).ofConv := by
  ext h
  have hp : h - algebraMap k H ((1 : WithConv (H →ₐ[k] k)).ofConv h) ∈
      RingHom.ker (1 : WithConv (H →ₐ[k] k)).ofConv := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      sub_self]
  have h1 := hx hp
  rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at h1
  rw [h1, AlgHom.convOne_apply, AlgHom.convOne_apply, Algebra.algebraMap_self, RingHom.id_apply]

end Unit

section Main

variable {k K : Type u} [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] [Algebra k K]

/-- **The `K`-side.** Given the rational-side contradiction, base change of a smooth affine
group scheme with trivial unipotent radical along an extension of algebraically closed fields
has trivial unipotent radical. -/
theorem hasTrivialUnipotentRadical_baseChange (hrat : RationalSideStatement.{u})
    (G : GroupScheme (Spec (CommRingCat.of k))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hG : HasTrivialUnipotentRadical G) :
    HasTrivialUnipotentRadical
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) := by
  classical
  intro H' i hi hsm hconn hU hN
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth H'.X.hom := hsm
  have : ConnectedSpace H'.X.left := hconn
  have : IsReduced H'.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      K H'.X.left H'.X.hom
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffineHom ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
  have : IsAffineHom H'.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  -- A closed embedding `ρ : G → GL_N` and the functions `u` cutting out unipotent matrices.
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  let M : Matrix (Fin N) (Fin N) Γ(G.X.left, ⊤) := (ρ.pointMatrix G.X (𝟙 G.X) : _)
  let u : Fin N × Fin N → AffineCoordinates.hopfAlgebra G :=
    fun p => coordEquiv G (((M - 1) ^ N) p.1 p.2)
  -- The group `S` of `K`-points of `H'`, as algebra maps out of the Hopf algebra of `G`.
  let R := (SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of K))))
  let S : Subgroup (WithConv (AffineCoordinates.hopfAlgebra G →ₐ[k] K)) :=
    R.comap (extPointEquiv G).toMonoidHom
  have : R.Normal := ⟨fun x hx g => hN _ g x (Subgroup.mem_top g) hx⟩
  have : S.Normal := Subgroup.Normal.comap inferInstance _
  have : Group.IsSolvable (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H'.X) :=
    isSolvable_points_of_isUnipotent hU _
  have : Group.IsSolvable ((yonedaGrp.obj H').obj
      (Opposite.op (Over.mk (𝟙 (Spec (CommRingCat.of K)))))) :=
    ‹Group.IsSolvable (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H'.X)›
  have : Group.IsSolvable R :=
    Group.isSolvable_of_surjective
      ((yonedaGrp.map i).app
        (Opposite.op (Over.mk (𝟙 (Spec (CommRingCat.of K)))))).hom.rangeRestrict_surjective
  have : Group.IsSolvable S :=
    Group.isSolvable_of_isSolvable_injective
      ((extPointEquiv G).toMonoidHom.subgroupComap_injective R (extPointEquiv G).injective)
  -- Points of `S` kill the functions `u`.
  have hu : ∀ p, ∀ x : AffineCoordinates.hopfAlgebra G →ₐ[k] K, toConv x ∈ S → x (u p) = 0 := by
    intro p x hx
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 hx
    change y ≫ i.hom.hom = extPointEquiv G (toConv x) at hy
    let σ : MatrixRepresentation H' (Fin N) :=
      i ≫ (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map ρ ≫
        (GeneralLinear.baseChangeIso (Fin N) (Spec.map (CommRingCat.ofHom (algebraMap k K)))).hom
    have h0 := MatrixRepresentation.pointMatrix_sub_one_pow_eq_zero_of_isUnipotent hU σ _ y
    have hσ : σ.pointMatrix _ y = ρ.pointMatrix _
        ((extIso k K).hom ≫ hopfPointEquiv G K (toConv x)) := by
      rw [MatrixRepresentation.pointMatrix_apply, MatrixRepresentation.pointMatrix_apply]
      simp only [σ, Grp.comp_hom_hom]
      rw [← Category.assoc, ← Category.assoc, GeneralLinear.pointsEquiv_comp_baseChangeIso_hom,
        baseChangePointsEquiv_comp, hy, baseChangePointsEquiv_extPointEquiv]
    have h1 := pointMatrix_sub_one_pow_apply ρ N
      ((extIso k K).hom ≫ hopfPointEquiv G K (toConv x)) p.1 p.2
    rw [← hσ, h0] at h1
    have h2 : ((extIso k K).hom ≫ hopfPointEquiv G K (toConv x)).left =
        Spec.map (CommRingCat.ofHom x.toRingHom) ≫ (schemeIso G).hom := by
      rw [Over.comp_left, hopfPointEquiv_left]
      simp [extIso]
    rw [h2] at h1
    have h3 := appTop_point G K x
      ((((ρ.pointMatrix G.X (𝟙 G.X) : Matrix (Fin N) (Fin N) Γ(G.X.left, ⊤)) - 1) ^ N) p.1 p.2)
    have h4 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv (x (u p)) = 0 := h3.symm.trans h1.symm
    exact (ΓSpecIso_inv_eq_zero_iff _ _).1 h4
  -- Points separate `K ⊗[k] H`.
  have : Algebra.Smooth k (AffineCoordinates.hopfAlgebra G) :=
    AffineCoordinates.smooth_algebra G inferInstance
  have : IsReduced (K ⊗[k] AffineCoordinates.hopfAlgebra G) :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_of_domain K _
  have hsep : ∀ t : K ⊗[k] AffineCoordinates.hopfAlgebra G,
      (∀ x : AffineCoordinates.hopfAlgebra G →ₐ[k] K, extPoint x t = 0) → t = 0 :=
    eq_zero_of_forall_extPoint
  -- The prime `Q` of `K ⊗[k] H` cut out by `H'`.
  have : (BorelExistence.coordinateKernel i).IsPrime := BorelExistence.coordinateKernel_isPrime i
  let Q : Ideal (K ⊗[k] AffineCoordinates.hopfAlgebra G) :=
    Ideal.comap (theta K G) (BorelExistence.coordinateKernel i)
  have hSQ : ∀ q, q ∈ Q ↔ ∀ x : AffineCoordinates.hopfAlgebra G →ₐ[k] K,
      toConv x ∈ S → extPoint x q = 0 := by
    intro q
    constructor
    · intro hq x hx
      obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 hx
      change y ≫ i.hom.hom = extPointEquiv G (toConv x) at hy
      have h2 : (y ≫ i.hom.hom).left.appTop (theta K G q) = 0 := by
        change y.left.appTop (i.hom.hom.left.appTop (theta K G q)) = 0
        rw [show i.hom.hom.left.appTop (theta K G q) = 0 from hq, map_zero]
      rw [hy, extPointEquiv_appTop_theta, ΓSpecIso_inv_eq_zero_iff] at h2
      exact h2
    · intro h
      change i.hom.hom.left.appTop (theta K G q) = 0
      apply eq_zero_of_forall_point (X := H'.X)
      intro z
      obtain ⟨x, hx⟩ := (extPointEquiv G).surjective (z ≫ i.hom.hom)
      have hxS : toConv x.ofConv ∈ S := by
        change extPointEquiv G x ∈ R
        rw [hx]
        exact SubgroupFunctor.mem_range.2 ⟨z, rfl⟩
      have h2 := extPointEquiv_appTop_theta G x q
      rw [hx, h _ hxS, map_zero] at h2
      exact h2
  -- The augmentation ideal `P`.
  let P : Ideal (AffineCoordinates.hopfAlgebra G) :=
    RingHom.ker (1 : WithConv (AffineCoordinates.hopfAlgebra G →ₐ[k] k)).ofConv
  have : P.IsPrime := RingHom.ker_isPrime _
  have hrange : ∀ x : AffineCoordinates.hopfAlgebra G →ₐ[k] K, P ≤ RingHom.ker x →
      toConv x ∈ S := by
    intro x hx
    rw [eq_one_of_ker_le x hx, toConv_ofConv]
    exact S.one_mem
  -- `Q` lies over `P`.
  have hQP : ∀ q ∈ Q, baseMap (K := K) (Ideal.Quotient.mkₐ k P) q = 0 := by
    intro q hq
    by_contra hr
    have : IsDomain ((AffineCoordinates.hopfAlgebra G ⧸ P) ⊗[k] K) :=
      P2MW.S_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed.GeomIntegralOfIsAlgClosed.isDomain_tensorProduct_of_isAlgClosed
        _ _
    have : IsDomain (K ⊗[k] (AffineCoordinates.hopfAlgebra G ⧸ P)) :=
      (Algebra.TensorProduct.comm k K _).toRingEquiv.toMulEquiv.isDomain _
    obtain ⟨φ, hφ⟩ := exists_algHom_ne_zero (K := K) hr
    let x : AffineCoordinates.hopfAlgebra G →ₐ[k] K := (φ.restrictScalars k).comp
      (Algebra.TensorProduct.includeRight.comp (Ideal.Quotient.mkₐ k P))
    have hext : extPoint x = φ.comp (baseMap (Ideal.Quotient.mkₐ k P)) := by
      apply Algebra.TensorProduct.ext'
      intro a h
      change extPoint x (a ⊗ₜ h) = φ (baseMap (Ideal.Quotient.mkₐ k P) (a ⊗ₜ h))
      rw [extPoint_tmul, baseMap_tmul]
      have : a ⊗ₜ[k] (Ideal.Quotient.mkₐ k P h) =
          a • ((1 : K) ⊗ₜ[k] (Ideal.Quotient.mkₐ k P h)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, map_smul, smul_eq_mul]
      rfl
    have hxP : P ≤ RingHom.ker x := by
      intro p hp
      rw [RingHom.mem_ker]
      change φ (1 ⊗ₜ[k] (Ideal.Quotient.mkₐ k P p)) = 0
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 hp, TensorProduct.tmul_zero,
        map_zero]
    have := (hSQ q).1 hq x (hrange x hxP)
    rw [hext] at this
    exact hφ this
  by_cases hlt : ∃ p ∈ P, (1 : K) ⊗ₜ[k] p ∉ Q
  · -- A nontrivial `S` descends to the data of the rational side.
    exfalso
    obtain ⟨𝔭, h𝔭, h𝔭P, Γ, hΓn, hΓs, hΓu, hΓmem⟩ :=
      exists_isPrime_lt_of_normal_solvable S u hsep hu Q hSQ P hQP hlt
    have hs : Function.Surjective (coordEquiv G) := (coordEquiv G).surjective
    have : 𝔭.IsPrime := h𝔭
    refine hrat k G hG (Fin N) ρ hρ (Ideal.comap (coordEquiv G) 𝔭) inferInstance ?_
      (Γ.map (rationalPointEquiv G).toMonoidHom)
      (Subgroup.Normal.map hΓn _ (rationalPointEquiv G).surjective)
      (Group.isSolvable_of_surjective
        ((rationalPointEquiv G).toMonoidHom.subgroupMap_surjective Γ)) ?_ ?_
    · rw [← map_one (rationalPointEquiv G), rationalPointEquiv_left, ker_appTop_point]
      refine lt_of_le_not_ge (Ideal.comap_mono h𝔭P.le) fun h => h𝔭P.not_ge ?_
      exact (Ideal.comap_le_comap_iff_of_surjective _ hs _ _).1 h
    · intro g hg
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hg
      refine ⟨N, ?_⟩
      ext a c
      have hzc : z.ofConv (u (a, c)) = 0 := hΓu z hz (a, c)
      have h1 : ((ρ.rationalMatrix (rationalPointEquiv G z) : Matrix (Fin N) (Fin N) k) - 1) ^ N =
          (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.mapMatrix
            (((ρ.pointMatrix (Over.mk (𝟙 (Spec (CommRingCat.of k)))) (rationalPointEquiv G z) :
              Matrix (Fin N) (Fin N) Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)) - 1) ^ N) := by
        rw [map_pow, map_sub, map_one]
        rfl
      have h2 := pointMatrix_sub_one_pow_apply ρ N (rationalPointEquiv G z) a c
      rw [rationalPointEquiv_left] at h2
      have h3 := appTop_point G k z.ofConv
        ((((ρ.pointMatrix G.X (𝟙 G.X) : Matrix (Fin N) (Fin N) Γ(G.X.left, ⊤)) - 1) ^ N) a c)
      have h4 : (Scheme.ΓSpecIso (CommRingCat.of k)).hom
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv (z.ofConv (u (a, c)))) = 0 := by
        rw [Iso.inv_hom_id_apply]
        exact hzc
      exact (congrFun (congrFun h1 a) c).trans
        ((congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom (h2.trans h3)).trans h4)
    · intro x hx
      obtain ⟨y, rfl⟩ := (rationalPointEquiv G).surjective x
      rw [rationalPointEquiv_left, ker_appTop_point] at hx
      exact ⟨y, hΓmem y.ofConv ((Ideal.comap_le_comap_iff_of_surjective _ hs _ _).1 hx), rfl⟩
  · -- Otherwise `S` is trivial, and so is the range of `i`.
    push Not at hlt
    have hS : ∀ x : AffineCoordinates.hopfAlgebra G →ₐ[k] K, toConv x ∈ S →
        x = (1 : WithConv (AffineCoordinates.hopfAlgebra G →ₐ[k] K)).ofConv := by
      intro x hx
      refine eq_one_of_ker_le x fun p hp => ?_
      have := (hSQ _).1 (hlt p hp) x hx
      rw [extPoint_tmul, one_mul] at this
      exact this
    have : IsSeparated ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G).X.hom :=
      inferInstance
    have hle := SubgroupFunctor.range_le_of_algClosed_points (i := i) (kernelUnit_isClosedSubgroup _)
      (by
        intro g hg
        obtain ⟨x, rfl⟩ := (extPointEquiv G).surjective g
        have hx : toConv x.ofConv ∈ S := hg
        rw [← toConv_ofConv x, hS _ hx, toConv_ofConv, map_one, range_kernelUnit]
        exact Subgroup.one_mem _)
    rw [range_kernelUnit] at hle
    refine le_antisymm hle fun T x hx => ?_
    have hx1 : x = 1 := hx
    subst hx1
    exact Subgroup.one_mem _

end Main

/-- The target statement, given the rational-side contradiction. -/
theorem algebraicallyClosedRadicalFieldExtensionStatement_of_rationalSide
    (hrat : RationalSideStatement.{u}) : AlgebraicallyClosedRadicalFieldExtensionStatement.{u} := by
  intro k K _ _ _ _ _ G hsm haff _ hG
  exact hasTrivialUnipotentRadical_baseChange hrat G hG

end Langlands.GroupScheme.RadicalFieldExtension
