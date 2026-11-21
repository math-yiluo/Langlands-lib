# Compact pullbacks in the quasi-étale site

Authors: Worker 964 and Worker 209.

`compactQuasiEtalePullbacks` proves `CompactQuasiEtalePullbacksStatement` at
independent field and space universes `u` and `v`. The proof adapts the geometric
part of the Library's `compactContinuousRelativePullback` without using its
action data.

1. For a site cospan `U ⟶ B ← V` over `X`, `localizedQuasiEtalePullback`
   constructs the localized products `P = U ×_X V` and `Q = B ×_X B` using
   the quasi-étale structure maps to `X`. The site arrow equations identify
   the maps in the first product with the composites through `B`.
2. `compactQuasiEtaleDiagonalDomain` identifies the diagonal `B ⟶ Q` with
   an analytic-domain embedding. `compactRelativePullbackOfDiagonal` pulls
   this domain back along the induced map `P ⟶ Q`. Its result `D` supplies
   a domain of `P`, compact Hausdorffness of its domain object, and the full
   localized `IsPullback` for the restricted projections over `B`. This
   step requires compact Hausdorffness of `B`, `U`, and `V`, not of `X` or of
   the auxiliary products.
3. The Hausdorff quasi-étale sources `U` and `V` give local domain–étale
   factorizations of their maps to `X`. `of_isPullback_common` supplies
   these factorizations for the common map `P ⟶ X`; `domainι_comp` restricts
   them to the cut. The resulting quasi-étaleness proves that the cut with
   structure map `i ≫ (p.1.snd ≫ V.hom)` is an actual object of
   `QuasiEtaleSite X`, where `i` is its domain inclusion into `P`.
4. The restricted projections are site arrows by the product equation over
   `X`. Their commutativity over `B` follows by `MorphismProperty.Over.Hom.ext`
   from `D.isPullback.w`. The resulting site cone has compact Hausdorff point
   by `D.compact`, and its underlying square is `D.isPullback`, with no
   restriction on the localized test object.

The proof handles arbitrary site arrows and adds no hypotheses. It does not
prove or assume the general quasi-étale stability clauses for composition,
base change, or morphisms over a common base.
