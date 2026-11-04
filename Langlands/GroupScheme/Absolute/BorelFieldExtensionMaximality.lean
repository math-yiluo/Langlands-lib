import Langlands.GroupScheme.Absolute.BorelFieldExtensionKSide
import Langlands.GroupScheme.Absolute.BorelFieldExtensionDescent
import Langlands.GroupScheme.AffineHopfCoordinates
import Langlands.GroupScheme.AffineCoordinatesFiniteType
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Absolute.RationalPointClosureSolvable
import Langlands.TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
import Langlands.GroupScheme.Absolute.UnipotentAllBorelsEnvelope
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed

/-! # Maximality of a Borel subgroup after an extension of algebraically closed fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open WithConv

namespace Langlands.GroupScheme.BorelFieldExtension

set_option backward.isDefEq.respectTransparency false

section Spec

/-- Pulling back a global function of `Spec R` coming from `R` along `Spec.map f`. -/
theorem specMap_appTop_inv {R S : CommRingCat.{u}} (f : R ⟶ S) (r : R) :
    (Spec.map f).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (f r) := by
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]

theorem ΓSpecIso_inv_eq_zero_iff (R : CommRingCat.{u}) (r : R) :
    (Scheme.ΓSpecIso R).inv r = 0 ↔ r = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  simpa using congrArg (fun y => (Scheme.ΓSpecIso R).hom y) h

end Spec

section PointEquiv

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

/-- The coordinate Hopf algebra of an affine group scheme of finite type is finitely generated. -/
instance hopfAlgebra_finiteType [LocallyOfFiniteType G.X.hom] :
    Algebra.FiniteType k (AffineCoordinates.hopfAlgebra G) :=
  AffineCoordinates.algebraFiniteType G

/-- Points of the coordinate Hopf algebra with values in a `k`-algebra `A` are the points of `G`
on `Spec A`. -/
def hopfPointEquiv (A : Type u) [CommRing A] [Algebra k A] :
    WithConv (AffineCoordinates.hopfAlgebra G →ₐ[k] A) ≃*
      ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of k)) ⟶ G.X) :=
  (Spec.mapMulEquiv (R := k) (S := AffineCoordinates.hopfAlgebra G) (T := A)).trans
    ((yonedaGrp.mapIso (AffineCoordinates.hopfSpecIso G)).app
      (op ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of k))))).groupIsoToMulEquiv

/-- The underlying scheme isomorphism `Spec H ≅ G` of the coordinate Hopf algebra `H`. -/
def schemeIso : Spec (CommRingCat.of (AffineCoordinates.hopfAlgebra G)) ≅ G.X.left :=
  (Over.forget _).mapIso ((Grp.forget _).mapIso (AffineCoordinates.hopfSpecIso G))

theorem hopfPointEquiv_left (A : Type u) [CommRing A] [Algebra k A]
    (x : WithConv (AffineCoordinates.hopfAlgebra G →ₐ[k] A)) :
    (hopfPointEquiv G A x).left =
      Spec.map (CommRingCat.ofHom x.ofConv.toRingHom) ≫ (schemeIso G).hom :=
  rfl

/-- Global functions on `G` are the coordinate Hopf algebra. -/
def coordEquiv : Γ(G.X.left, ⊤) ≃+* AffineCoordinates.hopfAlgebra G :=
  ((Scheme.Γ.mapIso (schemeIso G).op).trans
    (Scheme.ΓSpecIso (CommRingCat.of (AffineCoordinates.hopfAlgebra G)))).commRingCatIsoToRingEquiv

theorem coordEquiv_apply (g : Γ(G.X.left, ⊤)) :
    coordEquiv G g = (Scheme.ΓSpecIso (CommRingCat.of (AffineCoordinates.hopfAlgebra G))).hom
      ((schemeIso G).hom.appTop g) :=
  rfl

/-- Global functions evaluated along the point of `G` attached to an algebra map. -/
theorem appTop_point (A : Type u) [CommRing A] [Algebra k A]
    (x : AffineCoordinates.hopfAlgebra G →ₐ[k] A) (g : Γ(G.X.left, ⊤)) :
    (Spec.map (CommRingCat.ofHom x.toRingHom) ≫ (schemeIso G).hom).appTop g =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (x (coordEquiv G g)) := by
  have h := specMap_appTop_inv (CommRingCat.ofHom x.toRingHom) (coordEquiv G g)
  rw [coordEquiv_apply, Iso.hom_inv_id_apply] at h
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h]
  rfl

/-- The global functions killed by the point attached to `x` are the preimage of `ker x`. -/
theorem ker_appTop_point (A : Type u) [CommRing A] [Algebra k A]
    (x : AffineCoordinates.hopfAlgebra G →ₐ[k] A) :
    RingHom.ker (Spec.map (CommRingCat.ofHom x.toRingHom) ≫ (schemeIso G).hom).appTop.hom =
      Ideal.comap (coordEquiv G) (RingHom.ker x) := by
  ext g
  rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker]
  change (Spec.map (CommRingCat.ofHom x.toRingHom) ≫ (schemeIso G).hom).appTop g = 0 ↔ _
  rw [appTop_point, ΓSpecIso_inv_eq_zero_iff]

theorem schemeIso_hom_comp :
    (schemeIso G).hom ≫ G.X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k (AffineCoordinates.hopfAlgebra G))) :=
  Over.w ((Grp.forget _).map (AffineCoordinates.hopfSpecIso G).hom)

/-- Constants of the coordinate Hopf algebra are pulled back from the base. -/
theorem coordEquiv_symm_algebraMap (c : k) :
    (coordEquiv G).symm (algebraMap k (AffineCoordinates.hopfAlgebra G) c) =
      G.X.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := by
  apply (coordEquiv G).injective
  rw [RingEquiv.apply_symm_apply, coordEquiv_apply]
  have h1 : (schemeIso G).hom.appTop (G.X.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) =
      (Spec.map (CommRingCat.ofHom (algebraMap k (AffineCoordinates.hopfAlgebra G)))).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := by
    rw [← schemeIso_hom_comp]
    rfl
  rw [h1, specMap_appTop_inv, Iso.inv_hom_id_apply]
  rfl

end PointEquiv

section Points

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

variable (k) in
/-- The identity test scheme over `Spec k`, as the spectrum of `k` over itself. -/
def unitIso : Over.mk (𝟙 (Spec (CommRingCat.of k))) ≅
    (Spec (CommRingCat.of k)).asOver (Spec (CommRingCat.of k)) :=
  Over.isoMk (Iso.refl _) (by simp [specOverSpec_over])

/-- Rational points of `G` are `k`-algebra maps out of its coordinate Hopf algebra. -/
def rationalPointEquiv : WithConv (AffineCoordinates.hopfAlgebra G →ₐ[k] k) ≃*
    (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :=
  (hopfPointEquiv G k).trans (pointsMulEquivOfIso (unitIso k) G.X)

theorem rationalPointEquiv_left (x : WithConv (AffineCoordinates.hopfAlgebra G →ₐ[k] k)) :
    (rationalPointEquiv G x).left =
      Spec.map (CommRingCat.ofHom x.ofConv.toRingHom) ≫ (schemeIso G).hom := by
  change ((unitIso k).hom ≫ hopfPointEquiv G k x).left = _
  rw [Over.comp_left, hopfPointEquiv_left]
  simp [unitIso]

variable (k K) in
/-- The `K`-point test scheme of a base change, regarded over `Spec k`. -/
def extIso : (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj
      (Over.mk (𝟙 (Spec (CommRingCat.of K)))) ≅
    (Spec (CommRingCat.of K)).asOver (Spec (CommRingCat.of k)) :=
  Over.isoMk (Iso.refl _) (by simp [specOverSpec_over])

/-- `K`-points of the base change of `G` are `k`-algebra maps from the coordinate Hopf algebra
of `G` to `K`. -/
def extPointEquiv : WithConv (AffineCoordinates.hopfAlgebra G →ₐ[k] K) ≃*
    (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G).X) :=
  (hopfPointEquiv G K).trans ((pointsMulEquivOfIso (extIso k K) G.X).trans
    (baseChangePointsEquiv _ G _).symm)

theorem baseChangePointsEquiv_extPointEquiv
    (x : WithConv (AffineCoordinates.hopfAlgebra G →ₐ[k] K)) :
    baseChangePointsEquiv (Spec.map (CommRingCat.ofHom (algebraMap k K))) G _
        (extPointEquiv G x) = (extIso k K).hom ≫ hopfPointEquiv G K x := by
  rw [extPointEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

theorem extPointEquiv_left_fst (x : WithConv (AffineCoordinates.hopfAlgebra G →ₐ[k] K)) :
    (extPointEquiv G x).left ≫
        pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      Spec.map (CommRingCat.ofHom x.ofConv.toRingHom) ≫ (schemeIso G).hom := by
  rw [← baseChangePointsEquiv_left, baseChangePointsEquiv_extPointEquiv, Over.comp_left,
    hopfPointEquiv_left]
  simp [extIso]

theorem extPointEquiv_left_snd (x : WithConv (AffineCoordinates.hopfAlgebra G →ₐ[k] K)) :
    (extPointEquiv G x).left ≫
        pullback.snd G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) = 𝟙 _ :=
  Over.w (extPointEquiv G x)

end Points

section Theta

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

variable (K) in
/-- Scalars of `K` as global functions on the base change of `G`. -/
def scalarHom : K →+* Γ(((GroupScheme.baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G).X.left, ⊤) :=
  (pullback.snd G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

variable (K) in
/-- Coordinates of `G` as global functions on the base change of `G`. -/
def coordHom : AffineCoordinates.hopfAlgebra G →+* Γ(((GroupScheme.baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G).X.left, ⊤) :=
  (pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop.hom.comp
    (coordEquiv G).symm.toRingHom

theorem scalarHom_algebraMap (c : k) :
    scalarHom K G (algebraMap k K c) =
      coordHom K G (algebraMap k (AffineCoordinates.hopfAlgebra G) c) := by
  change (pullback.snd G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv (algebraMap k K c)) =
    (pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop
      ((coordEquiv G).symm (algebraMap k _ c))
  rw [coordEquiv_symm_algebraMap]
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv (algebraMap k K c) =
      (Spec.map (CommRingCat.ofHom (algebraMap k K))).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) :=
    (specMap_appTop_inv (CommRingCat.ofHom (algebraMap k K)) c).symm
  rw [h1]
  change (pullback.snd G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k K))).appTop _ =
    (pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫ G.X.hom).appTop _
  rw [pullback.condition]

variable (K) in
/-- The `k`-algebra structure on global functions of the base change of `G`, through the
coordinates of `G`. -/
abbrev baseChangeAlgebra : Algebra k Γ(((GroupScheme.baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G).X.left, ⊤) :=
  ((coordHom K G).comp (algebraMap k (AffineCoordinates.hopfAlgebra G))).toAlgebra

attribute [local instance] baseChangeAlgebra

variable (K) in
/-- The comparison map from `K ⊗[k] H` to global functions on the base change of `G`. -/
def theta : K ⊗[k] AffineCoordinates.hopfAlgebra G →+* Γ(((GroupScheme.baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G).X.left, ⊤) :=
  (Algebra.TensorProduct.productMap
    { scalarHom K G with commutes' := fun c => scalarHom_algebraMap G c }
    { coordHom K G with commutes' := fun _ => rfl }).toRingHom

theorem theta_tmul (a : K) (h : AffineCoordinates.hopfAlgebra G) :
    theta K G (a ⊗ₜ h) = scalarHom K G a * coordHom K G h :=
  Algebra.TensorProduct.productMap_apply_tmul _ _ _ _

/-- Evaluating `theta` at a `K`-point is the scalar extension of the point. -/
theorem extPointEquiv_appTop_theta (x : WithConv (AffineCoordinates.hopfAlgebra G →ₐ[k] K))
    (q : K ⊗[k] AffineCoordinates.hopfAlgebra G) :
    (extPointEquiv G x).left.appTop (theta K G q) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv (extPoint x.ofConv q) := by
  induction q using TensorProduct.inductionOn with
  | tmul a h =>
    rw [theta_tmul, map_mul, extPoint_tmul, map_mul]
    congr 1
    · change ((extPointEquiv G x).left ≫
          pullback.snd G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a) = _
      rw [extPointEquiv_left_snd]
      rfl
    · change ((extPointEquiv G x).left ≫
          pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop
          ((coordEquiv G).symm h) = _
      rw [extPointEquiv_left_fst]
      refine (appTop_point G K x.ofConv ((coordEquiv G).symm h)).trans ?_
      rw [RingEquiv.apply_symm_apply]
  | add q r hq hr => rw [map_add, map_add, hq, hr, map_add, map_add]

end Theta

section Nullstellensatz

open P2MW.S_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed.GeomIntegralOfIsAlgClosed in
/-- A nonzero element of a finitely generated domain over an algebraically closed field survives
at some rational point. -/
theorem exists_algHom_ne_zero {K : Type u} [Field K] [IsAlgClosed K] {R : Type u} [CommRing R]
    [IsDomain R] [Algebra K R] [Algebra.FiniteType K R] {r : R} (hr : r ≠ 0) :
    ∃ φ : R →ₐ[K] K, φ r ≠ 0 := by
  have : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)
  have hbot : (⊥ : Ideal R).jacobson = ⊥ :=
    isJacobsonRing_iff_prime_eq.1 this ⊥ Ideal.isPrime_bot
  have hr' : r ∉ (⊥ : Ideal R).jacobson := by
    rw [hbot]
    exact fun h => hr (Ideal.mem_bot.1 h)
  rw [Ideal.jacobson, Ideal.mem_sInf] at hr'
  push Not at hr'
  obtain ⟨m, ⟨-, hm⟩, hrm⟩ := hr'
  exact ⟨pointOfMaximal K m, fun h => hrm ((pointOfMaximal_eq_zero_iff m r).1 h)⟩

/-- On a reduced scheme locally of finite type over an algebraically closed field, a global
function vanishing at every rational point is zero. -/
theorem eq_zero_of_forall_point {K : Type u} [Field K] [IsAlgClosed K]
    {X : Over (Spec (CommRingCat.of K))} [IsReduced X.left] [LocallyOfFiniteType X.hom]
    (g : Γ(X.left, ⊤))
    (h : ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X, z.left.appTop g = 0) : g = 0 := by
  by_contra hg
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hne : (X.left.basicOpen g : Set X.left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro he
    apply hg
    rw [← basicOpen_eq_bot_iff]
    exact SetLike.coe_injective (he.trans TopologicalSpace.Opens.coe_bot.symm)
  obtain ⟨x, hxU, hx⟩ :=
    nonempty_inter_closedPoints hne (X.left.basicOpen g).isOpen.isLocallyClosed
  have hx' : IsClosed {x} := hx
  have hz : (pointOfClosedPoint X.hom x hx').appTop g = 0 :=
    h (Over.homMk (pointOfClosedPoint X.hom x hx') (pointOfClosedPoint_comp X.hom x hx'))
  have hmem : (IsLocalRing.closedPoint K : Spec (CommRingCat.of K)) ∈
      (pointOfClosedPoint X.hom x hx') ⁻¹ᵁ X.left.basicOpen g := by
    rw [Scheme.Hom.mem_preimage, pointOfClosedPoint_apply]
    exact hxU
  rw [Scheme.preimage_basicOpen_top, hz, Scheme.basicOpen_zero] at hmem
  simp at hmem

end Nullstellensatz

section Main

variable {k K : Type u} [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] [Algebra k K]
  {G B : GroupScheme (Spec (CommRingCat.of k))} {i : B ⟶ G}

variable (i) in
/-- The ideal of the subgroup `i` in the coordinate Hopf algebra of `G`. -/
def hopfKernel [IsAffine G.X.left] : Ideal (AffineCoordinates.hopfAlgebra G) :=
  Ideal.comap (coordEquiv G).symm (BorelExistence.coordinateKernel i)

omit [IsAlgClosed k] [IsAlgClosed K] in
/-- A `K`-point of `G` killing the ideal of `B` is a `K`-point of the base change of `B`. -/
theorem extPointEquiv_mem_range [IsAffine G.X.left] (hi : IsClosedSubgroup i)
    (x : AffineCoordinates.hopfAlgebra G →ₐ[k] K) (hx : hopfKernel i ≤ RingHom.ker x) :
    extPointEquiv G (toConv x) ∈ (SubgroupFunctor.range
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i)).carrier _ := by
  rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.mem_baseChange,
    baseChangePointsEquiv_extPointEquiv, SubgroupFunctor.mem_range]
  have : IsClosedImmersion i.hom.hom.left := hi
  have key : BorelExistence.coordinateKernel i ≤
      RingHom.ker (hopfPointEquiv G K (toConv x)).left.appTop.hom := by
    rw [hopfPointEquiv_left, ker_appTop_point]
    intro c hc
    apply hx
    change (coordEquiv G).symm (coordEquiv G c) ∈ BorelExistence.coordinateKernel i
    rw [RingEquiv.symm_apply_apply]
    exact hc
  have hker : i.hom.hom.left.ker ≤ (hopfPointEquiv G K (toConv x)).left.ker := by
    rw [Scheme.ker_of_isAffine, Scheme.ker_of_isAffine]
    exact (map_le_map_iff Scheme.IdealSheafData.equivOfIsAffine.symm).2 key
  refine ⟨(extIso k K).hom ≫ Over.homMk (IsClosedImmersion.lift _ _ hker) ?_, ?_⟩
  · rw [← Over.w i.hom.hom, IsClosedImmersion.lift_fac_assoc]
    exact Over.w (hopfPointEquiv G K (toConv x))
  · rw [Category.assoc]
    congr 1
    ext1
    simp

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- The maximality field of a Borel subgroup survives an extension of algebraically closed
fields. -/
theorem maximal_baseChange (hi : IsBorelSubgroup i)
    (B' : GroupScheme (Spec (CommRingCat.of K)))
    (i' : B' ⟶ (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)
    (f : (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj B ⟶ B')
    (hi' : IsClosedSubgroup i') (hsm : Smooth B'.X.hom) (hconn : ConnectedSpace B'.X.left)
    (hsolv : IsSolvableGroupScheme B')
    (hf : f ≫ i' = (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i) :
    IsIso f := by
  classical
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth B.X.hom := hi.smooth
  have : ConnectedSpace B.X.left := hi.connectedSpace
  have : Smooth B'.X.hom := hsm
  have : ConnectedSpace B'.X.left := hconn
  have : IsReduced B'.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      K B'.X.left B'.X.hom
  have hiK : IsClosedSubgroup
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i) :=
    hi.isClosedSubgroup.baseChange _
  -- The group `S` of `K`-points of `B'`, as algebra maps out of the Hopf algebra of `G`.
  let R := (SubgroupFunctor.range i').carrier (Over.mk (𝟙 (Spec (CommRingCat.of K))))
  let S : Subgroup (WithConv (AffineCoordinates.hopfAlgebra G →ₐ[k] K)) :=
    R.comap (extPointEquiv G).toMonoidHom
  have : Group.IsSolvable (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ B'.X) :=
    (isSolvableGroupScheme_iff_isSolvable_points B').1 hsolv
  have : Group.IsSolvable ((yonedaGrp.obj B').obj (op (Over.mk (𝟙 (Spec (CommRingCat.of K)))))) :=
    ‹Group.IsSolvable (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ B'.X)›
  have : Group.IsSolvable R :=
    Group.isSolvable_of_surjective
      ((yonedaGrp.map i').app (op (Over.mk (𝟙 (Spec (CommRingCat.of K)))))).hom.rangeRestrict_surjective
  have : Group.IsSolvable S :=
    Group.isSolvable_of_isSolvable_injective
      ((extPointEquiv G).toMonoidHom.subgroupComap_injective R (extPointEquiv G).injective)
  have hrange : ∀ x : AffineCoordinates.hopfAlgebra G →ₐ[k] K,
      hopfKernel i ≤ RingHom.ker x → toConv x ∈ S := by
    intro x hx
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 (extPointEquiv_mem_range hi.isClosedSubgroup x hx)
    refine SubgroupFunctor.mem_range.2 ⟨y ≫ f.hom.hom, ?_⟩
    change (y ≫ f.hom.hom) ≫ i'.hom.hom = extPointEquiv G (toConv x)
    rw [← hy, ← hf, Category.assoc]
    rfl
  -- The prime `Q` of `K ⊗[k] H` cut out by `B'`.
  have : (BorelExistence.coordinateKernel i').IsPrime := BorelExistence.coordinateKernel_isPrime i'
  let Q : Ideal (K ⊗[k] AffineCoordinates.hopfAlgebra G) :=
    Ideal.comap (theta K G) (BorelExistence.coordinateKernel i')
  have hSQ : ∀ q, q ∈ Q ↔ ∀ x : AffineCoordinates.hopfAlgebra G →ₐ[k] K,
      toConv x ∈ S → extPoint x q = 0 := by
    intro q
    constructor
    · intro hq x hx
      obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 hx
      change y ≫ i'.hom.hom = extPointEquiv G (toConv x) at hy
      have h2 : (y ≫ i'.hom.hom).left.appTop (theta K G q) = 0 := by
        change y.left.appTop (i'.hom.hom.left.appTop (theta K G q)) = 0
        rw [show i'.hom.hom.left.appTop (theta K G q) = 0 from hq, map_zero]
      rw [hy, extPointEquiv_appTop_theta, ΓSpecIso_inv_eq_zero_iff] at h2
      exact h2
    · intro h
      change i'.hom.hom.left.appTop (theta K G q) = 0
      apply eq_zero_of_forall_point (X := B'.X)
      intro z
      obtain ⟨x, hx⟩ := (extPointEquiv G).surjective (z ≫ i'.hom.hom)
      have hxS : toConv x.ofConv ∈ S := by
        change extPointEquiv G x ∈ R
        rw [hx]
        exact SubgroupFunctor.mem_range.2 ⟨z, rfl⟩
      have h2 := extPointEquiv_appTop_theta G x q
      rw [hx, h _ hxS, map_zero] at h2
      exact h2
  have : (hopfKernel i).IsPrime := by
    have := BorelExistence.coordinateKernel_isPrime i
    unfold hopfKernel
    infer_instance
  -- `Q` lies over the ideal of `B`.
  have hQP : ∀ q ∈ Q, baseMap (K := K) (Ideal.Quotient.mkₐ k (hopfKernel i)) q = 0 := by
    intro q hq
    by_contra hr
    have : IsDomain ((AffineCoordinates.hopfAlgebra G ⧸ hopfKernel i) ⊗[k] K) :=
      P2MW.S_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed.GeomIntegralOfIsAlgClosed.isDomain_tensorProduct_of_isAlgClosed
        _ _
    have : IsDomain (K ⊗[k] (AffineCoordinates.hopfAlgebra G ⧸ hopfKernel i)) :=
      (Algebra.TensorProduct.comm k K _).toRingEquiv.toMulEquiv.isDomain _
    obtain ⟨φ, hφ⟩ := exists_algHom_ne_zero (K := K) hr
    let x : AffineCoordinates.hopfAlgebra G →ₐ[k] K := (φ.restrictScalars k).comp
      (Algebra.TensorProduct.includeRight.comp (Ideal.Quotient.mkₐ k (hopfKernel i)))
    have hext : extPoint x = φ.comp (baseMap (Ideal.Quotient.mkₐ k (hopfKernel i))) := by
      apply Algebra.TensorProduct.ext'
      intro a h
      change extPoint x (a ⊗ₜ h) = φ (baseMap (Ideal.Quotient.mkₐ k (hopfKernel i)) (a ⊗ₜ h))
      rw [extPoint_tmul, baseMap_tmul]
      have : a ⊗ₜ[k] (Ideal.Quotient.mkₐ k (hopfKernel i) h) =
          a • ((1 : K) ⊗ₜ[k] (Ideal.Quotient.mkₐ k (hopfKernel i) h)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, map_smul, smul_eq_mul]
      rfl
    have hxP : hopfKernel i ≤ RingHom.ker x := by
      intro p hp
      rw [RingHom.mem_ker]
      change φ (1 ⊗ₜ[k] (Ideal.Quotient.mkₐ k (hopfKernel i) p)) = 0
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 hp, TensorProduct.tmul_zero,
        map_zero]
    have := (hSQ q).1 hq x (hrange x hxP)
    rw [hext] at this
    exact hφ this
  by_cases hlt : ∃ p ∈ hopfKernel i, (1 : K) ⊗ₜ[k] p ∉ Q
  · -- A proper descent would produce a solvable group of rational points strictly larger
    -- than the one of `B`.
    exfalso
    obtain ⟨𝔭, h𝔭, hlt𝔭, Γ, hΓ, hΓmem⟩ :=
      exists_isPrime_lt_of_solvable S Q hSQ (hopfKernel i) hQP hlt
    let Γ' := Γ.map (rationalPointEquiv G).toMonoidHom
    have : Group.IsSolvable Γ' :=
      Group.isSolvable_of_surjective ((rationalPointEquiv G).toMonoidHom.subgroupMap_surjective Γ)
    have h𝔭' : Ideal.comap (coordEquiv G) 𝔭 ≤ BorelExistence.coordinateKernel i := by
      intro c hc
      have := hlt𝔭.le hc
      rwa [hopfKernel, Ideal.mem_comap, RingEquiv.symm_apply_apply] at this
    have hle := coordinateKernel_le_of_solvable_points hi (Ideal.comap (coordEquiv G) 𝔭) h𝔭' Γ' (by
      intro z hz
      obtain ⟨y, rfl⟩ := (rationalPointEquiv G).surjective z
      refine ⟨y, hΓmem y.ofConv ?_, rfl⟩
      intro p hp
      have h1 : (coordEquiv G).symm p ∈ RingHom.ker (rationalPointEquiv G y).left.appTop.hom := by
        apply hz
        change coordEquiv G ((coordEquiv G).symm p) ∈ 𝔭
        rwa [RingEquiv.apply_symm_apply]
      rw [rationalPointEquiv_left, ker_appTop_point, Ideal.mem_comap,
        RingEquiv.apply_symm_apply] at h1
      exact h1)
    apply hlt𝔭.not_ge
    intro p hp
    have := hle (show (coordEquiv G).symm p ∈ BorelExistence.coordinateKernel i from hp)
    change coordEquiv G ((coordEquiv G).symm p) ∈ 𝔭 at this
    rwa [RingEquiv.apply_symm_apply] at this
  · -- Otherwise every `K`-point of `B'` is one of `B_K`, and `B'` factors through `B_K`.
    push Not at hlt
    have hpts : ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ B'.X,
        z ≫ i'.hom.hom ∈ (SubgroupFunctor.range
          ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i)).carrier
            _ := by
      intro z
      obtain ⟨x, hx⟩ := (extPointEquiv G).surjective (z ≫ i'.hom.hom)
      have hxS : toConv x.ofConv ∈ S := by
        change extPointEquiv G x ∈ R
        rw [hx]
        exact SubgroupFunctor.mem_range.2 ⟨z, rfl⟩
      have hP : hopfKernel i ≤ RingHom.ker x.ofConv := by
        intro p hp
        have := (hSQ _).1 (hlt p hp) x.ofConv hxS
        rw [extPoint_tmul, one_mul] at this
        exact this
      rw [← hx]
      exact extPointEquiv_mem_range hi.isClosedSubgroup x.ofConv hP
    obtain ⟨a, ha⟩ :=
      UnipotentAllBorelsEnvelope.exists_factor_of_algClosed_points i'.hom.hom hiK hpts
    refine BorelExistence.isIso_of_coordinateKernel_eq _ i' f hiK hi' hf
      (le_antisymm ?_ (BorelExistence.coordinateKernel_le _ i' f hf))
    intro c hc
    have hc' : ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
        i).hom.hom.left.appTop c = 0 := hc
    change i'.hom.hom.left.appTop c = 0
    rw [← ha]
    change a.left.appTop (((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i).hom.hom.left.appTop c) = 0
    rw [hc', map_zero]

end Main

end Langlands.GroupScheme.BorelFieldExtension
