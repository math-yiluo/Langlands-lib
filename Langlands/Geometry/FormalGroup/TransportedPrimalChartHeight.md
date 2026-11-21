# Integral coordinate transport of the primal chart rank

`BasicAtlas.OrderAction.RationalHom.onChart_isoTransport` evaluates the actual transported tensor over any test algebra where the target chart is defined. The result is the original evaluated tensor conjugated by the two integral chart isomorphisms. The equality follows by applying the chart composition law twice and evaluating each integral coordinate change.

`restrictCentralQuasiIsogeny_chartRank_transport` starts from actual local retractions of the two formal order projectors and from integral comparisons with the chosen central atlases. It pulls the scalar-kernel ranks of the chosen atlases back through the chart isomorphisms. The prime and central chart comparison then measures the actual restricted local quasi-isogeny with a signed prime height \(k\) divisible by the residue degree \(f\). Evaluating the transported central tensor gives the height function \(k/f\) on the same test spectrum. Both functions retain their actual local kernel-rank witnesses.

The formal projector calculation is a derived step for the primal restriction of the split polarized rigidifier in Rapoport–Zink (1996), §6.43 and (6.17), printed pp. 308–309 (PDF pp. 320–321). The prime height convention is in Harris (1997), Appendix, printed pp. 112–113 (PDF pp. 38–39), including item (iii) on the polarized rigidifier.
